module

public import Mathlib

/-!
# Turán density existence and the graph case

Supporting results for Erdős Problem 712.
The compared statements prove existence and bounds for the limiting density,
and evaluate it for graphs (uniformity two). They do not determine the values
for k > r > 2 and do not solve the general open problem.

Reference: https://www.erdosproblems.com/712
-/

@[expose] public section

open Finset Filter Topology

namespace Erdos712

/-- A uniform family with no complete r-uniform hypergraph on k vertices. -/
def IsAdmissible (n r k : ℕ) (H : Finset (Finset (Fin n))) : Prop :=
  (∀ e ∈ H, e.card = r) ∧ ∀ S : Finset (Fin n), S.card = k → ¬ S.powersetCard r ⊆ H

open Classical in
/-- The maximum number of edges in such a family. -/
noncomputable def ex (n r k : ℕ) : ℕ :=
  (((univ : Finset (Fin n)).powersetCard r).powerset.filter (IsAdmissible n r k)).sup Finset.card

/-- The limiting density, whose convergence is asserted below. -/
noncomputable def turanDensity (r k : ℕ) : ℝ :=
  limUnder atTop fun n => (ex n r k : ℝ) / n.choose r

/-- The normalized extremal numbers converge. -/
theorem tendsto_turanDensity (r k : ℕ) :
    Tendsto (fun n => (ex n r k : ℝ) / n.choose r) atTop (𝓝 (turanDensity r k)) := by
  sorry

theorem turanDensity_nonneg (r k : ℕ) : 0 ≤ turanDensity r k := by
  sorry

theorem turanDensity_le_one (r k : ℕ) : turanDensity r k ≤ 1 := by
  sorry

/-- For graphs the binomial normalization gives 1 - 1/(k-1). -/
theorem tendsto_ex_two_div_choose (k : ℕ) (hk : 2 ≤ k) :
    Tendsto (fun n : ℕ => (ex n 2 k : ℝ) / n.choose 2) atTop
      (𝓝 (1 - 1 / ((k : ℝ) - 1))) := by
  sorry

theorem turanDensity_two (k : ℕ) (hk : 2 ≤ k) :
    turanDensity 2 k = 1 - 1 / ((k : ℝ) - 1) := by
  sorry

/-- The square normalization contributes a factor of one half. -/
theorem tendsto_ex_two_div_sq (k : ℕ) (hk : 2 ≤ k) :
    Tendsto (fun n : ℕ => (ex n 2 k : ℝ) / (n : ℝ) ^ 2) atTop
      (𝓝 ((1 / 2) * (1 - 1 / ((k : ℝ) - 1)))) := by
  sorry

end Erdos712
