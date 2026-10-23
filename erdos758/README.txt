Erdos 758: the twelve-vertex case, z(12)=4

This is an attributed reproduction and module port of the existing proof at
plby/lean-proofs commit8822f7ddef30fadbd92e1c6ab4ed897af356af5e.
Informal computation: Bhavik Mehta. Original formal authors: Codex/GPT-5.6 Sol.
AItoBit maintains this vendored port and submission packaging.
No new mathematical discovery is claimed.

Exact target: every graph on12 vertices has a partition into at most4 clique
or independent classes, and an explicit12-vertex graph cannot use3 classes.
This proves z12=4. It does not formalize the entire1..19 table or determine20.

Challenge.lean and Solution.lean independently declare the same target name,
Erdos758Palomar.main. Do not import them together. Challenge has one deliberate
sorry required for the comparison target; Solution proves the result using the
fully vendored source and has no proof holes. comparator.json compares main only.
There is no FormalConjecturesUtil dependency: Mathlib is the sole dependency.

The package includes94 ported source modules and275 unchanged CNF/LRAT/ids
assets. The LRAT proofs and graph-semantic bridges are checked by Lean; the
SAT solver used to discover certificates is not a trusted theorem assumption.
PORT-INVENTORY.txt records the mechanical module changes. Private declarations,
source headers and original proof bodies are preserved.

Lean4.33.1 and Mathlib0df444a360eaa60ab8c11dca51a86af692955474 are pinned.
Reproduction commands after dependencies are available:
  lake exe cache get
  lake build Solution
  lake build Challenge
Fresh port compilation and Palomar comparator/preflight are still required.
The preparation of this package alone is not a successful verification claim.

Resource control: the91 certificate case modules add prerequisite imports in
two acyclic lanes (sorted case i imports i-2). Unbounded parallel certificate
builds exhausted runner memory; two-worker builds passed. These proof-neutral
imports constrain Lake scheduling to at most two certificate cases at once.
They add no mathematical axiom. Fresh compilation of this port is required.
