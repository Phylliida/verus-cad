# verus-cad

## MCP: Verus Proof Index

This project has a Verus MCP server (`verus-mcp`) that indexes all spec/proof/exec functions, types, traits, and impls across the codebase. Prefer these tools when searching for Verus items:

### Function Search
- `search(query, details?)` — Browse functions by name substring. Ranked: exact > prefix > substring. Includes fuzzy fallback when few results found. Set `details=true` for full signatures with requires/ensures (default limit drops to 10).
- `search_ensures(query)` — Find lemmas that prove a specific property. Clause snippets centered around match.
- `search_requires(query)` — Find what preconditions a lemma needs.
- `search_signature(param_type, return_type, type_bound)` — Find functions by type signature.
- `search_body(query)` — Find functions that call a specific lemma or use a pattern in their body.
- `search_doc(query)` — Search within doc comments of functions and types.
- `lookup(name)` — Get full details (signature, requires/ensures, file, module) for a single function or type.
- `batch_lookup(names)` — Look up multiple functions/types by exact name in one call (max 10). Returns full signatures.

### Type & Trait Search
- `search_types(query)` — Browse structs, enums, and type aliases by name substring.
- `search_trait(name)` — Show trait definition + all implementors.
- `browse_module(path)` — List all functions and types in a module (exact or prefix match).

### Dependency Tracking
- `find_dependencies(name, direction?)` — Call graph: "callers" (default) or "callees".

### Utilities
- `list_modules()` — See all indexed modules grouped by crate.
- `stats()` — Show index statistics: counts by kind (spec/proof/exec), by crate, and assume(false) proof debt.
- `reindex()` — Force rebuild index. **Not normally needed** — the server auto-reindexes when `.rs` files change (500ms debounce).

**Workflow:** Use `search` / `search_ensures` / `search_requires` to browse, then `lookup` or `batch_lookup` to drill into specific functions. Use `search(query, details=true)` when you want full details inline without a separate lookup call.

All search tools accept optional `limit` (default 50) and `offset` (default 0) parameters for pagination.

`search_ensures`, `search_requires`, `search_body`, and `search_types` also accept optional `crate_name` and `module` filters.

`search_ensures`, `search_requires`, `search_body`, and `search_doc` queries support regex (e.g., `div.*mul.*eqv`). If the query isn't valid regex, it falls back to plain substring matching. All regex is case-insensitive.

`search_ensures`, `search_requires`, `search_body`, and `search_doc` also accept optional `name` filter to combine name + clause/body/doc search (e.g., find functions named "*cancel*" whose ensures mentions "eqv").
