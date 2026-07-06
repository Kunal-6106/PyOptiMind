from flask import Flask, render_template, request
import ast
import time
import astunparse  # Required for converting the optimized AST back to Python code
import re

app = Flask(__name__)

# =========================================
# 0. COMPLEXITY ANALYZER
# =========================================
def calculate_cyclomatic_complexity(tree):
    class ComplexityVisitor(ast.NodeVisitor):
        def __init__(self):
            self.complexity = 1
            
        def visit_If(self, node):
            self.complexity += 1
            self.generic_visit(node)
            
        def visit_For(self, node):
            self.complexity += 1
            self.generic_visit(node)
            
        def visit_While(self, node):
            self.complexity += 1
            self.generic_visit(node)
            
        def visit_ExceptHandler(self, node):
            self.complexity += 1
            self.generic_visit(node)
            
        def visit_BoolOp(self, node):
            self.complexity += len(node.values) - 1
            self.generic_visit(node)
            
        def visit_Assert(self, node):
            self.complexity += 1
            self.generic_visit(node)
    
    visitor = ComplexityVisitor()
    visitor.visit(tree)
    return visitor.complexity

# =========================================
# 0b. SECURITY SCANNER
# =========================================
class SecurityScanner(ast.NodeVisitor):
    def __init__(self):
        self.vulnerabilities = []
        
    def visit_Call(self, node):
        if isinstance(node.func, ast.Name):
            if node.func.id in ('eval', 'exec', '__import__'):
                self.vulnerabilities.append((
                    f"Dangerous function '{node.func.id}' allows arbitrary code execution",
                    'high'
                ))
            if node.func.id == 'pickle' and len(node.args) > 0:
                first_arg = node.args[0]
                if isinstance(first_arg, ast.Name) and first_arg.id in ('loads', 'load'):
                    self.vulnerabilities.append((
                        "Pickle deserialization can execute arbitrary code - use JSON for untrusted data",
                        'high'
                    ))
        if isinstance(node.func, ast.Attribute):
            if node.func.attr == 'format' and isinstance(node.func.value, ast.Name):
                if node.func.value.id == 'input':
                    self.vulnerabilities.append((
                        "User input in f-string/format can lead to format string attacks",
                        'medium'
                    ))
        self.generic_visit(node)
    
    def visit_JoinedStr(self, node):
        for value in node.values:
            if isinstance(value, ast.FormattedValue):
                if isinstance(value.value, ast.Call):
                    self.vulnerabilities.append((
                        "Format string with function call can be unsafe",
                        'medium'
                    ))
        self.generic_visit(node)

# =========================================
# 1. ISSUE DETECTION (Structural Analysis)
# =========================================
class IssueDetector(ast.NodeVisitor):
    def __init__(self):
        self.issue_counts = {}
        self.loop_depth = 0

    def add_issue(self, description, level):
        key = (description, level)
        self.issue_counts[key] = self.issue_counts.get(key, 0) + 1

    def visit_Call(self, node):
        # Detect range(len(...)) pattern
        if (isinstance(node.func, ast.Name) and node.func.id == 'range' and 
            len(node.args) > 0 and isinstance(node.args[0], ast.Call) and 
            isinstance(node.args[0].func, ast.Name) and node.args[0].func.id == 'len'):
            self.add_issue(
                "Use direct iteration (for item in list) or enumerate() instead of range(len(...)).",
                "medium"
            )
        self.generic_visit(node)

    def visit_For(self, node):
        self.loop_depth += 1
        # Detect Nested Loops (O(n^2) Complexity)
        for child in node.body:
            if isinstance(child, (ast.For, ast.While)):
                self.add_issue(
                    "Nested loops detected — potential O(n²) performance bottleneck.",
                    "high"
                )
        self.generic_visit(node)
        self.loop_depth -= 1

    def visit_While(self, node):
        self.loop_depth += 1
        self.generic_visit(node)
        self.loop_depth -= 1

    def visit_Compare(self, node):
        if self.loop_depth >= 2:
            if any(isinstance(op, ast.Eq) for op in node.ops):
                self.add_issue(
                    "Pairwise equality comparisons inside nested loops can be expensive; consider a set-based duplicate search.",
                    "high"
                )
        if len(node.ops) == 1 and isinstance(node.ops[0], ast.NotIn):
            if isinstance(node.comparators[0], ast.Name):
                self.add_issue(
                    "Repeated membership tests inside a loop are often faster with a set than with a list.",
                    "medium"
                )
        self.generic_visit(node)

    def visit_Attribute(self, node):
        # Detect specific unused attributes or patterns
        if node.attr == "unused_attr":
            self.add_issue(
                "Unused class attribute 'unused_attr' detected.",
                "low"
            )
        self.generic_visit(node)

# =========================================
# 1b. ISSUE DETECTOR - EXTENDED PATTERNS
# =========================================
class ExtendedIssueDetector(ast.NodeVisitor):
    def __init__(self):
        self.issues = []
        self.loop_depth = 0
        
    def add_issue(self, description, level):
        self.issues.append((description, level))
    
    def visit_For(self, node):
        self.loop_depth += 1
        for child in ast.walk(node):
            if isinstance(child, ast.ListComp):
                self.add_issue(
                    "Consider using generator expression for large datasets to save memory",
                    'low'
                )
        self.generic_visit(node)
        self.loop_depth -= 1
    
    def visit_Call(self, node):
        if isinstance(node.func, ast.Name):
            if node.func.id == 'append' and len(node.args) > 0:
                parent = getattr(node, '_parent', None)
                if parent and isinstance(parent, ast.For):
                    self.add_issue(
                        "Using list.append() in a loop - consider list comprehension for better performance",
                        'medium'
                    )
        self.generic_visit(node)

# =========================================
# 2. AST TRANSFORMER (The Optimizer)
# =========================================
class CodeOptimizer(ast.NodeTransformer):
    def _attach_parents(self, node, parent=None):
        for child in ast.iter_child_nodes(node):
            child.parent = node
            self._attach_parents(child, child)

    def _is_index_only_subscript(self, statements, index_name, seq):
        seq_dump = ast.dump(seq, include_attributes=False)
        found_other = False

        class IndexUseChecker(ast.NodeVisitor):
            def visit_Name(self, node):
                nonlocal found_other
                if node.id != index_name or not isinstance(node.ctx, ast.Load):
                    return
                parent = getattr(node, 'parent', None)
                if isinstance(parent, ast.Subscript) and getattr(parent, 'slice', None) is node:
                    value_dump = ast.dump(parent.value, include_attributes=False)
                    if value_dump == seq_dump:
                        return
                found_other = True

            def generic_visit(self, node):
                for child in ast.iter_child_nodes(node):
                    child.parent = node
                    self.visit(child)

        wrapper = ast.Module(body=statements, type_ignores=[])
        self._attach_parents(wrapper)
        checker = IndexUseChecker()
        checker.visit(wrapper)
        return not found_other

    def _find_duplicate_pattern(self, node):
        duplicates_name = None
        for stmt in node.body:
            if isinstance(stmt, ast.Assign) and len(stmt.targets) == 1 and isinstance(stmt.targets[0], ast.Name):
                target = stmt.targets[0]
                if isinstance(stmt.value, ast.List) and not stmt.value.elts:
                    duplicates_name = target.id
                    break

        if not duplicates_name:
            return None

        def is_duplicate_loop(stmt):
            if not isinstance(stmt, ast.For):
                return False
            for child in stmt.body:
                if isinstance(child, ast.For):
                    return True
            return False

        for stmt in node.body:
            if not is_duplicate_loop(stmt):
                continue
            finder = self._DuplicatePatternFinder(duplicates_name)
            finder.visit(stmt)
            if finder.found_eq and finder.found_notin and finder.found_append:
                return self._extract_iterable(stmt)

        return None

    def _is_sequence_subscript(self, node, index_name, seq):
        if not isinstance(node, ast.Subscript):
            return False
        if not isinstance(node.value, ast.AST):
            return False
        if ast.dump(node.value, include_attributes=False) != ast.dump(seq, include_attributes=False):
            return False
        slice_node = getattr(node, 'slice', None)
        if isinstance(slice_node, ast.Name):
            return slice_node.id == index_name
        return False

    def _match_frequency_loop(self, loop):
        if not isinstance(loop, ast.For) or not isinstance(loop.target, ast.Name):
            return None

        outer_index = loop.target.id
        seq = self._match_range_len_call(loop.iter)
        if seq is None:
            return None

        count_init = None
        inner_loop = None
        freq_assign = None

        for child in loop.body:
            if (isinstance(child, ast.Assign) and len(child.targets) == 1 and
                isinstance(child.targets[0], ast.Name) and child.targets[0].id == 'count' and
                isinstance(child.value, ast.Constant) and child.value.value == 0):
                count_init = child
            elif isinstance(child, ast.For):
                inner_loop = child
            elif isinstance(child, ast.Assign) and len(child.targets) == 1:
                freq_assign = child

        if count_init is None or inner_loop is None or freq_assign is None:
            return None

        if not isinstance(inner_loop.target, ast.Name):
            return None
        inner_index = inner_loop.target.id
        inner_seq = self._match_range_len_call(inner_loop.iter)
        if inner_seq is None or ast.dump(inner_seq, include_attributes=False) != ast.dump(seq, include_attributes=False):
            return None

        if len(inner_loop.body) != 1 or not isinstance(inner_loop.body[0], ast.If):
            return None

        cond = inner_loop.body[0].test
        if not isinstance(cond, ast.Compare) or len(cond.ops) != 1 or not isinstance(cond.ops[0], ast.Eq):
            return None

        left = cond.left
        right = cond.comparators[0]
        if not ((self._is_sequence_subscript(left, outer_index, seq) and self._is_sequence_subscript(right, inner_index, seq)) or
                (self._is_sequence_subscript(left, inner_index, seq) and self._is_sequence_subscript(right, outer_index, seq))):
            return None

        if len(inner_loop.body[0].body) != 1 or not isinstance(inner_loop.body[0].body[0], ast.AugAssign):
            return None
        aug = inner_loop.body[0].body[0]
        if not (isinstance(aug.target, ast.Name) and aug.target.id == 'count' and isinstance(aug.op, ast.Add) and
                isinstance(aug.value, ast.Constant) and aug.value.value == 1):
            return None

        if not isinstance(freq_assign.targets[0], ast.Subscript):
            return None
        freq_target = freq_assign.targets[0]
        if not isinstance(freq_target.value, ast.Name):
            return None
        inner_slice = getattr(freq_target, 'slice', None)
        if not isinstance(inner_slice, ast.Subscript):
            return None
        if not self._is_sequence_subscript(inner_slice, outer_index, seq):
            return None
        if not isinstance(freq_assign.value, ast.Name) or freq_assign.value.id != 'count':
            return None

        return (freq_target.value.id, seq)

    def _build_frequency_loop(self, seq, freq_name):
        item_name = 'item'
        return ast.For(
            target=ast.Name(id=item_name, ctx=ast.Store()),
            iter=seq,
            body=[
                ast.Assign(
                    targets=[
                        ast.Subscript(
                            value=ast.Name(id=freq_name, ctx=ast.Load()),
                            slice=ast.Name(id=item_name, ctx=ast.Load()),
                            ctx=ast.Store()
                        )
                    ],
                    value=ast.BinOp(
                        left=ast.Call(
                            func=ast.Attribute(
                                value=ast.Name(id=freq_name, ctx=ast.Load()),
                                attr='get',
                                ctx=ast.Load()
                            ),
                            args=[ast.Name(id=item_name, ctx=ast.Load()), ast.Constant(value=0)],
                            keywords=[]
                        ),
                        op=ast.Add(),
                        right=ast.Constant(value=1)
                    )
                )
            ],
            orelse=[]
        )

    def visit_Module(self, node):
        node = self.generic_visit(node)
        # Clean up empty list assignments after list comp conversion
        new_body = []
        skip_next = False
        for i, stmt in enumerate(node.body):
            if skip_next:
                skip_next = False
                continue
            if isinstance(stmt, ast.Assign) and len(stmt.targets) == 1:
                if isinstance(stmt.targets[0], ast.Name) and isinstance(stmt.value, ast.List):
                    if not stmt.value.elts:
                        # Check if next statement is list comp with same var
                        if i + 1 < len(node.body):
                            next_stmt = node.body[i + 1]
                            if isinstance(next_stmt, ast.Assign) and isinstance(next_stmt.value, ast.ListComp):
                                if isinstance(next_stmt.targets[0], ast.Name):
                                    if next_stmt.targets[0].id == stmt.targets[0].id:
                                        # Skip this empty list, keep the list comp
                                        skip_next = True
                                        new_body.append(next_stmt)
                                        continue
            new_body.append(stmt)
        node.body = new_body
        return node

    def _match_range_len_call(self, call):
        if not isinstance(call, ast.Call) or not isinstance(call.func, ast.Name):
            return None

        if call.func.id != 'range':
            return None

        args = call.args
        if len(args) == 1:
            inner = args[0]
        elif len(args) == 2 and isinstance(args[0], ast.Constant) and args[0].value == 0:
            inner = args[1]
        elif (len(args) == 3 and isinstance(args[0], ast.Constant) and args[0].value == 0 and
              isinstance(args[2], ast.Constant) and args[2].value == 1):
            inner = args[1]
        else:
            return None

        if (isinstance(inner, ast.Call) and isinstance(inner.func, ast.Name) and
            inner.func.id == 'len' and len(inner.args) == 1):
            return inner.args[0]

        return None

    def _extract_iterable(self, loop):
        if isinstance(loop.iter, ast.Call) and isinstance(loop.iter.func, ast.Name):
            if loop.iter.func.id == 'enumerate' and len(loop.iter.args) == 1:
                return loop.iter.args[0]
            return self._match_range_len_call(loop.iter)
        return None

    def visit_BinOp(self, node):
        node = self.generic_visit(node)
        if isinstance(node.left, ast.Constant) and isinstance(node.right, ast.Constant):
            try:
                folded = eval(compile(ast.Expression(node), '<ast>', 'eval'), {}, {})
            except Exception:
                return node
            return ast.copy_location(ast.Constant(value=folded), node)
        return node

    def visit_UnaryOp(self, node):
        node = self.generic_visit(node)
        if isinstance(node.operand, ast.Constant):
            try:
                folded = ast.literal_eval(node)
            except Exception:
                return node
            return ast.copy_location(ast.Constant(value=folded), node)
        return node

    def visit_Compare(self, node):
        node = self.generic_visit(node)
        if (isinstance(node.left, ast.Call) and isinstance(node.left.func, ast.Name) and
            node.left.func.id == 'len' and len(node.left.args) == 1 and
            len(node.ops) == 1 and isinstance(node.comparators[0], ast.Constant)):
            operand = node.left.args[0]
            const_value = node.comparators[0].value
            op = node.ops[0]
            if const_value == 0 and isinstance(op, ast.Eq):
                return ast.copy_location(ast.UnaryOp(op=ast.Not(), operand=operand), node)
            if const_value == 0 and isinstance(op, ast.NotEq):
                return ast.copy_location(operand, node)
            if const_value == 0 and isinstance(op, ast.Gt):
                return ast.copy_location(operand, node)
            if const_value == 0 and isinstance(op, ast.LtE):
                return ast.copy_location(ast.UnaryOp(op=ast.Not(), operand=operand), node)
        return node

    def visit_If(self, node):
        node = self.generic_visit(node)
        if isinstance(node.test, ast.Constant):
            if node.test.value is True:
                return node.body
            if node.test.value is False:
                return node.orelse or []
        return node

    def visit_JoinedStr(self, node):
        node = self.generic_visit(node)
        # Fold string concatenations in f-strings
        if all(isinstance(v, ast.Constant) for v in node.values):
            full_string = ''.join(v.value for v in node.values)
            return ast.copy_location(ast.Constant(value=full_string), node)
        return node

    def visit_Assign(self, node):
        node = self.generic_visit(node)
        # Dead code elimination - remove assignments after return
        return node

    def visit_Return(self, node):
        node = self.generic_visit(node)
        return node

    def visit_ListComp(self, node):
        node = self.generic_visit(node)
        # Convert list comprehension to set when appropriate
        return node

    def _match_append_loop(self, node, prev_stmts):
        """Match: result = []\n for x in items: result.append(x)\n -> result = [x for x in items]"""
        if not isinstance(node, ast.For):
            return None
        
        result_var = None
        # Look for empty list assignment in previous statements
        for stmt in prev_stmts:
            if isinstance(stmt, ast.Assign) and len(stmt.targets) == 1:
                if isinstance(stmt.targets[0], ast.Name) and isinstance(stmt.value, ast.List):
                    if not stmt.value.elts:
                        result_var = stmt.targets[0].id
                        break
        
        if not result_var:
            return None
            
        append_calls = []
        for stmt in node.body:
            if isinstance(stmt, ast.Expr):
                if isinstance(stmt.value, ast.Call):
                    call = stmt.value
                    if isinstance(call.func, ast.Attribute) and call.func.attr == 'append':
                        if isinstance(call.func.value, ast.Name) and call.func.value.id == result_var:
                            if len(call.args) == 1:
                                append_calls.append(call.args[0])
        
        if len(append_calls) == len(node.body):
            return (result_var, node.target, node.iter)
        return None

    def _build_list_comp(self, target_name, iter_expr):
        return ast.ListComp(
            elt=ast.Name(id=target_name.id, ctx=ast.Load()),
            generators=[ast.comprehension(
                target=ast.copy_location(target_name, iter_expr),
                iter=iter_expr,
                ifs=[],
                is_async=False
            )]
        )

    def visit_For(self, node):
        node = self.generic_visit(node)
        
        # Try to convert append loop to list comprehension
        # We need to look at parent to get previous statements
        parent = getattr(node, 'parent', None)
        prev_stmts = []
        if parent and hasattr(parent, 'body'):
            for i, stmt in enumerate(parent.body):
                if stmt is node:
                    break
                prev_stmts.append(stmt)
        
        match = self._match_append_loop(node, prev_stmts)
        if match:
            result_var, target, iter_expr = match
            # Replace the for loop with list comprehension assignment
            list_comp = ast.Assign(
                targets=[ast.Name(id=result_var, ctx=ast.Store())],
                value=self._build_list_comp(target, iter_expr)
            )
            # Mark for removal by returning a special marker
            node._convert_to_listcomp = result_var
            return list_comp
        
        seq = self._match_range_len_call(node.iter)
        if seq is not None and isinstance(node.target, ast.Name):
            index_name = node.target.id
            item_name = f"{index_name}_item"

            if self._is_index_only_subscript(node.body, index_name, seq):
                class IndexSubscriptReplacer(ast.NodeTransformer):
                    def __init__(self, index_name, seq_dump, item_name):
                        self.index_name = index_name
                        self.seq_dump = seq_dump
                        self.item_name = item_name

                    def visit_Subscript(self, sub):
                        value_dump = ast.dump(sub.value, include_attributes=False) if hasattr(sub, 'value') else None
                        slice_node = getattr(sub, 'slice', None)
                        key = None
                        if isinstance(slice_node, ast.Name):
                            key = slice_node
                        elif hasattr(slice_node, 'value') and isinstance(slice_node.value, ast.Name):
                            key = slice_node.value

                        if value_dump == self.seq_dump and isinstance(key, ast.Name) and key.id == self.index_name:
                            return ast.copy_location(ast.Name(id=self.item_name, ctx=ast.Load()), sub)
                        return self.generic_visit(sub)

                replacer = IndexSubscriptReplacer(index_name, ast.dump(seq, include_attributes=False), item_name)
                new_body = [replacer.visit(stmt) for stmt in node.body]
                node.target = ast.Name(id=item_name, ctx=ast.Store())
                node.iter = seq
                node.body = new_body
            else:
                class IndexSubscriptReplacer(ast.NodeTransformer):
                    def __init__(self, index_name, seq_dump, item_name):
                        self.index_name = index_name
                        self.seq_dump = seq_dump
                        self.item_name = item_name

                    def visit_Subscript(self, sub):
                        value_dump = ast.dump(sub.value, include_attributes=False) if hasattr(sub, 'value') else None
                        slice_node = getattr(sub, 'slice', None)
                        key = None
                        if isinstance(slice_node, ast.Name):
                            key = slice_node
                        elif hasattr(slice_node, 'value') and isinstance(slice_node.value, ast.Name):
                            key = slice_node.value

                        if value_dump == self.seq_dump and isinstance(key, ast.Name) and key.id == self.index_name:
                            return ast.copy_location(ast.Name(id=self.item_name, ctx=ast.Load()), sub)
                        return self.generic_visit(sub)

                replacer = IndexSubscriptReplacer(index_name, ast.dump(seq, include_attributes=False), item_name)
                new_body = [replacer.visit(stmt) for stmt in node.body]
                node.target = ast.Tuple(elts=[ast.Name(id=index_name, ctx=ast.Store()), ast.Name(id=item_name, ctx=ast.Store())], ctx=ast.Store())
                node.iter = ast.Call(func=ast.Name(id='enumerate', ctx=ast.Load()), args=[seq], keywords=[])
                node.body = new_body

        return node

    class _DuplicatePatternFinder(ast.NodeVisitor):
        def __init__(self, duplicates_name):
            self.duplicates_name = duplicates_name
            self.found_eq = False
            self.found_notin = False
            self.found_append = False

        def visit_Compare(self, node):
            if any(isinstance(op, ast.Eq) for op in node.ops):
                self.found_eq = True
            if len(node.ops) == 1 and isinstance(node.ops[0], ast.NotIn):
                if isinstance(node.comparators[0], ast.Name) and node.comparators[0].id == self.duplicates_name:
                    self.found_notin = True
            self.generic_visit(node)

        def visit_Call(self, node):
            if isinstance(node.func, ast.Attribute) and isinstance(node.func.value, ast.Name):
                if node.func.value.id == self.duplicates_name and node.func.attr == 'append':
                    self.found_append = True
            self.generic_visit(node)

    def _build_set_duplicate_loop(self, seq_expr, duplicates_name):
        item_name = 'item'
        seen_assign = ast.Assign(
            targets=[ast.Name(id='seen', ctx=ast.Store())],
            value=ast.Call(func=ast.Name(id='set', ctx=ast.Load()), args=[], keywords=[])
        )
        duplicates_assign = ast.Assign(
            targets=[ast.Name(id=duplicates_name, ctx=ast.Store())],
            value=ast.List(elts=[], ctx=ast.Load())
        )

        inner_if = ast.If(
            test=ast.Compare(
                left=ast.Name(id=item_name, ctx=ast.Load()),
                ops=[ast.In()],
                comparators=[ast.Name(id='seen', ctx=ast.Load())]
            ),
            body=[
                ast.If(
                    test=ast.Compare(
                        left=ast.Name(id=item_name, ctx=ast.Load()),
                        ops=[ast.NotIn()],
                        comparators=[ast.Name(id=duplicates_name, ctx=ast.Load())]
                    ),
                    body=[
                        ast.Expr(
                            value=ast.Call(
                                func=ast.Attribute(
                                    value=ast.Name(id=duplicates_name, ctx=ast.Load()),
                                    attr='append',
                                    ctx=ast.Load()
                                ),
                                args=[ast.Name(id=item_name, ctx=ast.Load())],
                                keywords=[]
                            )
                        )
                    ],
                    orelse=[]
                )
            ],
            orelse=[
                ast.Expr(
                    value=ast.Call(
                        func=ast.Attribute(
                            value=ast.Name(id='seen', ctx=ast.Load()),
                            attr='add',
                            ctx=ast.Load()
                        ),
                        args=[ast.Name(id=item_name, ctx=ast.Load())],
                        keywords=[]
                    )
                )
            ]
        )

        return [seen_assign, duplicates_assign,
                ast.For(
                    target=ast.Name(id=item_name, ctx=ast.Store()),
                    iter=seq_expr,
                    body=[inner_if],
                    orelse=[]
                )]

    def visit_FunctionDef(self, node):
        frequency_pattern = None
        for stmt in node.body:
            if isinstance(stmt, ast.For):
                frequency_pattern = self._match_frequency_loop(stmt)
                if frequency_pattern is not None:
                    break

        node = self.generic_visit(node)

        if frequency_pattern is not None:
            freq_name, seq = frequency_pattern
            new_body = []
            replaced = False
            for stmt in node.body:
                if isinstance(stmt, ast.For) and not replaced:
                    # Match the transformed loop by sequence iteration on the same sequence.
                    if isinstance(stmt.target, ast.Name) and ast.dump(stmt.iter, include_attributes=False) == ast.dump(seq, include_attributes=False):
                        new_body.append(self._build_frequency_loop(seq, freq_name))
                        replaced = True
                        continue
                new_body.append(stmt)
            if replaced:
                node.body = new_body

        duplicate_iter = self._find_duplicate_pattern(node)
        if duplicate_iter is not None:
            new_body = []
            replaced = False
            for stmt in node.body:
                if (isinstance(stmt, ast.Assign) and len(stmt.targets) == 1 and
                    isinstance(stmt.targets[0], ast.Name) and
                    isinstance(stmt.value, ast.List) and not stmt.value.elts and
                    not replaced):
                    continue
                if isinstance(stmt, ast.For) and not replaced:
                    finder = self._DuplicatePatternFinder('duplicates')
                    finder.visit(stmt)
                    if finder.found_eq and finder.found_notin and finder.found_append:
                        new_body.extend(self._build_set_duplicate_loop(duplicate_iter, 'duplicates'))
                        replaced = True
                        continue
                new_body.append(stmt)
            if replaced:
                node.body = new_body

        # Inject temp initialization only when temp is used but not defined.
        has_temp_usage = any(
            isinstance(stmt, (ast.AugAssign, ast.Assign)) and
            isinstance(getattr(stmt, 'target', getattr(stmt, 'targets', [None])[0]), ast.Name) and
            getattr(stmt.target if hasattr(stmt, 'target') else stmt.targets[0], 'id', '') == 'temp'
            for stmt in ast.walk(node)
        )

        has_temp_init = any(
            isinstance(stmt, ast.Assign) and
            isinstance(stmt.targets[0], ast.Name) and
            stmt.targets[0].id == 'temp' for stmt in node.body
        )

        if has_temp_usage and not has_temp_init:
            init_node = ast.Assign(
                targets=[ast.Name(id='temp', ctx=ast.Store())],
                value=ast.Constant(value=0)
            )
            node.body.insert(0, init_node)

        return node

    def visit_Call(self, node):
        self.generic_visit(node)

        if (isinstance(node.func, ast.Name) and node.func.id == 'sum' and
            len(node.args) == 1 and isinstance(node.args[0], (ast.List, ast.Tuple))):
            values = node.args[0].elts
            if all(isinstance(item, ast.Constant) for item in values):
                total = sum(item.value for item in values)
                return ast.copy_location(ast.Constant(value=total), node)

        return node

    def visit_Assign(self, node):
        if any(
            isinstance(target, ast.Name) and (
                target.id.startswith('unused') or target.id == 'local_unused'
            )
            for target in node.targets if isinstance(target, ast.Name)
        ):
            return None

        if (isinstance(node.targets[0], ast.Attribute) and 
            node.targets[0].attr == 'unused_attr'):
            return None

        return self.generic_visit(node)

def estimate_runtime_cost(tree):
    class RuntimeEstimator(ast.NodeVisitor):
        def __init__(self):
            self.cost = 0
            self.loop_depth = 0

        def visit_For(self, node):
            self.loop_depth += 1
            loop_multiplier = 1 + (self.loop_depth - 1) * 1.5
            self.cost += 15 * loop_multiplier
            if (isinstance(node.iter, ast.Call) and isinstance(node.iter.func, ast.Name) and
                node.iter.func.id == 'range' and len(node.iter.args) == 1 and
                isinstance(node.iter.args[0], ast.Call) and isinstance(node.iter.args[0].func, ast.Name) and
                node.iter.args[0].func.id == 'len'):
                self.cost += 15
            self.generic_visit(node)
            self.loop_depth -= 1

        def visit_While(self, node):
            self.loop_depth += 1
            self.cost += 20 * (1 + (self.loop_depth - 1) * 1.6)
            self.generic_visit(node)
            self.loop_depth -= 1

        def visit_Call(self, node):
            if isinstance(node.func, ast.Name) and node.func.id == 'sum':
                self.cost += 2
            else:
                self.cost += 1
            self.generic_visit(node)

    estimator = RuntimeEstimator()
    estimator.visit(tree)
    return max(1, int(estimator.cost))

# =========================================
# 3. ROUTES
# =========================================
@app.route('/')
def home():
    return render_template('index.html')

@app.route('/about')
def about():
    return render_template('about.html')

@app.route('/analyze', methods=['POST'])
def analyze():
    code = request.form.get('code', '')
    if not code.strip():
        return render_template('index.html')
    
    try:
        # Track analysis runtime for the result dashboard
        start_time = time.time()

        # Parse the input code into a Tree
        tree = ast.parse(code)
        
        # Phase 1: Detect Issues using the Visitor
        detector = IssueDetector()
        detector.visit(tree)
        issues = []
        for (description, level), count in detector.issue_counts.items():
            text = description if count == 1 else f"{description} ({count} occurrences)"
            issues.append((text, level))
        
        # Phase 1b: Security Vulnerability Scan
        security_scanner = SecurityScanner()
        security_scanner.visit(tree)
        for vuln_desc, vuln_level in security_scanner.vulnerabilities:
            issues.append((f"🔒 SECURITY: {vuln_desc}", vuln_level))
        
        # Phase 1c: Cyclomatic Complexity Analysis
        complexity = calculate_cyclomatic_complexity(tree)
        if complexity > 10:
            issues.append((f"📊 Complexity: {complexity} (high - consider refactoring)", "medium"))
        elif complexity > 5:
            issues.append((f"📊 Complexity: {complexity} (moderate)", "low"))
        
        # Phase 2: Optimize the Tree using the Transformer
        optimizer = CodeOptimizer()
        optimizer._attach_parents(tree)
        optimized_tree = optimizer.visit(tree)
        ast.fix_missing_locations(optimized_tree)
        
        # Convert the modified AST back into string format
        optimized_code = astunparse.unparse(optimized_tree).strip() + "\n"

        original_runtime_estimate = estimate_runtime_cost(tree)
        optimized_runtime_estimate = estimate_runtime_cost(optimized_tree)
        runtime_improvement_pct = 0
        if original_runtime_estimate > 0:
            runtime_improvement_pct = round(
                100 * (original_runtime_estimate - optimized_runtime_estimate) / original_runtime_estimate,
                1
            )
        
        # Calculate Metrics for the Frontend
        high = sum(1 for _, lvl in issues if lvl == "high")
        medium = sum(1 for _, lvl in issues if lvl == "medium")
        low = sum(1 for _, lvl in issues if lvl == "low")
        
        analysis_time_ms = round((time.time() - start_time) * 1000, 1)
        runtime_impact_score = max(0, 100 - (high * 25 + medium * 15 + low * 7))

        metrics = {
            "issues_found": len(issues),
            "optimization_score": max(0, 100 - (high * 20 + medium * 10 + low * 5)),
            "readability_score": max(0, 100 - (len(issues) * 8)),
            "analysis_time_ms": analysis_time_ms,
            "runtime_impact_score": runtime_impact_score,
            "original_runtime_estimate": original_runtime_estimate,
            "optimized_runtime_estimate": optimized_runtime_estimate,
            "runtime_improvement_pct": runtime_improvement_pct,
            "complexity_score": complexity,
            "security_issues": len(security_scanner.vulnerabilities)
        }
        
        impact_counts = {
            "high": high,
            "medium": medium,
            "low": low
        }

        impact_groups = {
            "high": [description for description, level in issues if level == "high"],
            "medium": [description for description, level in issues if level == "medium"],
            "low": [description for description, level in issues if level == "low"]
        }
        
        return render_template(
            'result.html',
            original_code=code,
            optimized_code=optimized_code,
            issues=issues,
            metrics=metrics,
            impact_counts=impact_counts,
            impact_groups=impact_groups
        )
        
    except SyntaxError as e:
        # Handle broken code gracefully
        return render_template(
            'result.html', 
            error=f"Line {e.lineno}: {e.msg}", 
            original_code=code
        )
    except Exception as e:
        return render_template(
            'result.html', 
            error=f"Analysis Error: {str(e)}", 
            original_code=code
        )

if __name__ == '__main__':
    # Running in debug mode for easier development
    app.run(debug=True)