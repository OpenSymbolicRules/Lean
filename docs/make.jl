using Documenter
using DocumenterLandingPage

# Stage only Markdown sources, keeping generated files out of future builds.
const pages = sort(filter(f -> endswith(f, ".md"), readdir(@__DIR__)))
mktempdir() do source
    for page in pages
        cp(joinpath(@__DIR__, page), joinpath(source, page))
    end
    makedocs(;
        root = @__DIR__,
        source,
        build = joinpath(@__DIR__, "build"),
        sitename = "OpenSymbolicRules — Lean",
        repo = Remotes.GitHub("OpenSymbolicRules", "Lean"),
        remotes = nothing,
        plugins = [LandingPage()],
        pages = ["index.md"; filter(!=("index.md"), pages)],
        format = Documenter.HTML(;
            edit_link = nothing,
            repolink = "https://github.com/OpenSymbolicRules/Lean",
            inventory_version = "0.1.0",
            canonical = "https://OpenSymbolicRules.github.io/Lean/",
        ),
    )
end

# Keep the complete Markdown documentation alongside the generated HTML.
open(joinpath(@__DIR__, "build", "llms.txt"), "w") do io
    println(io, "# OpenSymbolicRules — Lean\n")
    for page in pages
        title = replace(first(split(read(joinpath(@__DIR__, page), String), '\n')), r"^#+\s*" => "")
        url = page == "index.md" ? "./" : replace(page, ".md" => "/")
        println(io, "- [", title, "](", url, ")")
    end
end
open(joinpath(@__DIR__, "build", "llms-full.txt"), "w") do io
    for page in ["index.md"; filter(!=("index.md"), pages)]
        println(io, read(joinpath(@__DIR__, page), String), "\n")
    end
end
