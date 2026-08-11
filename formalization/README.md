# Lean formalization

This directory is a single Lake project supporting the accompanying paper.
Its public root is `FourPlayerXORGames.lean`.

The project imports `QIT` from the pinned public QuAIR/Lean-QIT revision in
`lakefile.toml`; Lean-QIT source code is not copied into this repository.

```bash
lake exe cache get
lake build FourPlayerXORGames
```

The source is organized into two namespaces:

- `QIT.XORGame`: finite weighted games, MERP and commuting-operator semantics,
  primitive-circuit lifting, ternary Hamming geometry, and the Klein witness;
- `QIT.Research.FourXOR`: Cayley translation matchings, PREFs, and the
  elementary-abelian all-length obstruction.

See [`FORMALIZATION.md`](FORMALIZATION.md) for the statement correspondence.
