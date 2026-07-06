function applyTheme(theme) {
    const html = document.documentElement;
    const body = document.body;
    const dark = theme === "dark";

    html.classList.toggle("dark-mode", dark);
    if (body) {
        body.classList.toggle("dark-mode", dark);
    }
}

function toggleTheme() {
    const currentlyDark = document.documentElement.classList.contains("dark-mode");
    const nextTheme = currentlyDark ? "light" : "dark";
    applyTheme(nextTheme);
    localStorage.setItem("theme", nextTheme);
}

window.addEventListener("DOMContentLoaded", () => {
    let savedTheme = localStorage.getItem("theme");
    if (!savedTheme && window.matchMedia) {
        savedTheme = window.matchMedia("(prefers-color-scheme: dark)").matches ? "dark" : "light";
    }

    applyTheme(savedTheme || "light");
    document.body.classList.add("loaded");

    const transitionLinks = document.querySelectorAll(".nav-transition");
    transitionLinks.forEach(link => {
        link.addEventListener("click", function (e) {
            const href = this.getAttribute("href");
            if (href && !href.startsWith("#") && href !== window.location.pathname) {
                e.preventDefault();
                document.body.classList.add("page-exit");
                setTimeout(() => {
                    window.location.href = href;
                }, 280);
            }
        });
    });

    window.addEventListener("pageshow", event => {
        if (event.persisted) {
            document.body.classList.add("loaded");
        }
    });
});