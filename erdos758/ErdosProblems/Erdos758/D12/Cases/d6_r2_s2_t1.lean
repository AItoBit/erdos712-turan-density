module

public import ErdosProblems.Erdos758.D12.Semantic
public import ErdosProblems.Erdos758.D12.Cases.d6_r2_s1_t3

@[expose] public section

namespace Erdos758.D12Certificate

lrat_proof d6_r2_s2_t1_raw
  (include_str "../reduced/d6_r2_s2_t1.cnf")
  (include_str "../reduced/d6_r2_s2_t1.lrat")

def d6_r2_s2_t1_ids : String := include_str "../reduced/d6_r2_s2_t1.ids"

def d6_r2_s2_t1_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, false), (8, false),
    (9, false), (10, false), (11, false), (12, true), (13, true), (14, false), (15, false),
    (16, false), (17, true), (18, true), (19, false), (20, false), (21, false), (23, true),
    (24, false), (25, false)]

private theorem d6_r2_s2_t1_sem_0_2739 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s2_t1_ids, d6_r2_s2_t1_units, edge, 0, 2739) := by
  exact d12CaseRangeProof(d6_r2_s2_t1_ids, d6_r2_s2_t1_units, edge, 0, 2739)

theorem d6_r2_s2_t1 (edge : Nat → Prop) : D12Outcome edge d6_r2_s2_t1_units := by
  exact d6_r2_s2_t1_sem_0_2739 edge (d12CaseRaw(d6_r2_s2_t1_raw, edge))

end Erdos758.D12Certificate
