module

public import Mathlib

/-!
# Erdős Problem #712 (hypergraph Turán densities)

Determine, for any `k > r > 2`, the value of `lim ex_r(n, K_k^r) / (n choose r)`, where
`ex_r(n, K_k^r)` is the largest number of `r`-edges which can be placed on `n` vertices so that
there exists no set of `k` vertices which is covered by all `k choose r` possible `r`-edges.

## Contents

* `IsAdmissible`, `ex`, `turanDensity`: the objects in the problem.
* `tendsto_turanDensity`: the limit exists for every `r`, `k` (via the averaging argument
  `ex_succ_mul_le`: `ex(n, ·) / (n choose r)` is non-increasing for `n ≥ r`), and
  `0 ≤ turanDensity r k ≤ 1`.
* `IsSolution`: the problem statement (what it means for `answer r k` to be the value of the
  limit for all `k > r > 2`), and `isSolution_iff`: the solutions are exactly the functions that
  agree with `turanDensity` on `k > r > 2`. Finding a closed form is open; nothing here claims it.
* `turanDensity_two`, `tendsto_ex_two_div_sq`: Turán's case `r = 2`.

Note on normalisation: with the normalisation `ex / (n choose 2)` used in the problem, Turán's
limit for `r = 2` is `1 - 1/(k-1)` (`turanDensity_two`); the value `½ (1 - 1/(k-1))` quoted on the
problem page is the limit of `ex / n^2` (`tendsto_ex_two_div_sq`).
-/

@[expose] public section

open Finset Filter Topology

namespace Erdos712

/-- An `r`-uniform hypergraph `H` on the vertex set `Fin n` (a family of `r`-element subsets)
is *admissible* (i.e. `K_k^r`-free) if no `k`-element set of vertices has all of its
`k choose r` subsets of size `r` in `H`. -/
def IsAdmissible (n r k : ℕ) (H : Finset (Finset (Fin n))) : Prop :=
  (∀ e ∈ H, e.card = r) ∧ ∀ S : Finset (Fin n), S.card = k → ¬ S.powersetCard r ⊆ H

open Classical in
/-- `ex n r k = ex_r(n, K_k^r)`: the largest number of `r`-edges on `n` vertices such that no
`k` vertices are covered by all `k choose r` possible `r`-edges. -/
noncomputable def ex (n r k : ℕ) : ℕ :=
  (((univ : Finset (Fin n)).powersetCard r).powerset.filter (IsAdmissible n r k)).sup Finset.card

/-- The hypergraph Turán density `π(K_k^r) = lim_{n → ∞} ex_r(n, K_k^r) / (n choose r)`
(see `tendsto_turanDensity` for the existence of the limit). -/
noncomputable def turanDensity (r k : ℕ) : ℝ :=
  limUnder atTop fun n => (ex n r k : ℝ) / n.choose r

lemma card_le_ex {n r k : ℕ} {H : Finset (Finset (Fin n))} (hH : IsAdmissible n r k H) :
    H.card ≤ ex n r k := by
  classical
  unfold ex
  convert Finset.le_sup (f := Finset.card) (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 ?_, hH⟩)
  intro e he
  simp [hH.1 e he]

lemma ex_le_choose (n r k : ℕ) : ex n r k ≤ n.choose r := by
  classical
  unfold ex
  refine Finset.sup_le fun H hH => ?_
  simp only [mem_filter, mem_powerset] at hH
  simpa using Finset.card_le_card hH.1

lemma exists_eq_ex (n r k : ℕ) (h : 0 < ex n r k) :
    ∃ H, IsAdmissible n r k H ∧ H.card = ex n r k := by
  classical
  unfold ex at *
  set s := (((univ : Finset (Fin n)).powersetCard r).powerset.filter (IsAdmissible n r k))
  have hs : s.Nonempty := by
    by_contra hne; rw [Finset.not_nonempty_iff_eq_empty] at hne; rw [hne] at h; simp at h
  obtain ⟨H, hH, he⟩ := Finset.exists_mem_eq_sup s hs Finset.card
  exact ⟨H, (mem_filter.1 hH).2, he.symm⟩

/-- Deleting a vertex `v` from an admissible hypergraph on `n + 1` vertices leaves an admissible
hypergraph on `n` vertices. -/
lemma card_filter_not_mem_le {n r k : ℕ} {H : Finset (Finset (Fin (n + 1)))}
    (hH : IsAdmissible (n + 1) r k H) (v : Fin (n + 1)) :
    (H.filter (fun e => v ∉ e)).card ≤ ex n r k := by
  classical
  set f := v.succAboveEmb
  set H' : Finset (Finset (Fin n)) :=
    (univ : Finset (Finset (Fin n))).filter (fun e => e.map f ∈ H)
  have hmap : H'.map (mapEmbedding f).toEmbedding = H.filter (fun e => v ∉ e) := by
    ext e
    simp only [H', Finset.mem_map, mem_filter, mem_univ, true_and, RelEmbedding.coe_toEmbedding,
      mapEmbedding_apply]
    constructor
    · rintro ⟨e', he', rfl⟩
      refine ⟨he', ?_⟩
      simp [f, Fin.succAbove_ne]
    · rintro ⟨he, hv⟩
      have hsub : e ⊆ (univ : Finset (Fin n)).map f := by
        intro x hx
        obtain ⟨y, rfl⟩ := Fin.exists_succAbove_eq (x := x) (y := v) (by rintro rfl; exact hv hx)
        simp [f]
      obtain ⟨u, -, rfl⟩ := Finset.subset_map_iff.1 hsub
      exact ⟨u, he, rfl⟩
  rw [← hmap, card_map]
  apply card_le_ex
  refine ⟨fun e he => ?_, fun S hS hsub => ?_⟩
  · have := hH.1 _ (mem_filter.1 he).2
    simpa using this
  · apply hH.2 (S.map f) (by simpa using hS)
    rw [powersetCard_map]
    intro T hT
    rw [Finset.mem_map] at hT
    obtain ⟨T', hT', rfl⟩ := hT
    exact (mem_filter.1 (hsub hT')).2

/-- Averaging (Katona–Nemetz–Simonovits): `(n + 1 - r) ex(n+1) ≤ (n + 1) ex(n)`. -/
lemma ex_succ_mul_le (n r k : ℕ) : ex (n + 1) r k * (n + 1 - r) ≤ (n + 1) * ex n r k := by
  classical
  rcases Nat.eq_zero_or_pos (ex (n + 1) r k) with h | h
  · simp [h]
  obtain ⟨H, hH, hc⟩ := exists_eq_ex _ _ _ h
  rw [← hc]
  calc H.card * (n + 1 - r) = ∑ e ∈ H, (univ.filter (fun v : Fin (n + 1) => v ∉ e)).card := by
        rw [sum_congr rfl (g := fun _ => n + 1 - r), sum_const, smul_eq_mul]
        intro e he
        rw [filter_not, filter_mem_eq_inter, univ_inter, card_sdiff, inter_univ, hH.1 e he]
        simp
    _ = ∑ v : Fin (n + 1), (H.filter (fun e => v ∉ e)).card := by
        simp only [card_filter]
        exact sum_comm
    _ ≤ ∑ _v : Fin (n + 1), ex n r k := sum_le_sum fun v _ => card_filter_not_mem_le hH v
    _ = (n + 1) * ex n r k := by simp

lemma antitoneOn_ex_div_choose (r k : ℕ) :
    AntitoneOn (fun n => (ex n r k : ℝ) / n.choose r) (Set.Ici r) := by
  apply antitoneOn_nat_Ici_of_succ_le
  intro n hn
  have h1 : 0 < n.choose r := Nat.choose_pos hn
  have h2 : 0 < (n + 1).choose r := Nat.choose_pos (by omega)
  have key : ex (n + 1) r k * n.choose r ≤ ex n r k * (n + 1).choose r := by
    have hpos : 0 < n + 1 - r := by omega
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc ex (n + 1) r k * n.choose r * (n + 1 - r)
        = ex (n + 1) r k * (n + 1 - r) * n.choose r := by ring
      _ ≤ (n + 1) * ex n r k * n.choose r := Nat.mul_le_mul_right _ (ex_succ_mul_le n r k)
      _ = ex n r k * (n.choose r * (n + 1)) := by ring
      _ = ex n r k * (n + 1).choose r * (n + 1 - r) := by rw [Nat.choose_mul_succ_eq]; ring
  rw [div_le_div_iff₀ (by exact_mod_cast h2) (by exact_mod_cast h1)]
  exact_mod_cast key

/-- The limit defining the hypergraph Turán density exists. -/
theorem tendsto_turanDensity (r k : ℕ) :
    Tendsto (fun n => (ex n r k : ℝ) / n.choose r) atTop (𝓝 (turanDensity r k)) := by
  let f := fun n => (ex n r k : ℝ) / n.choose r
  suffices h : ∃ x, Tendsto (fun n => f (n + r)) atTop (𝓝 x) by
    obtain ⟨x, hx⟩ := h
    have hx' : Tendsto f atTop (𝓝 x) := (tendsto_add_atTop_iff_nat r).1 hx
    show Tendsto f atTop (𝓝 (limUnder atTop f))
    rw [hx'.limUnder_eq]
    exact hx'
  refine ⟨⨅ n, f (n + r), tendsto_atTop_ciInf ?_ ⟨0, ?_⟩⟩
  · intro a b hab
    exact antitoneOn_ex_div_choose r k (by simp) (by simp) (by omega)
  · rintro _ ⟨n, rfl⟩
    positivity

theorem turanDensity_nonneg (r k : ℕ) : 0 ≤ turanDensity r k :=
  ge_of_tendsto' (tendsto_turanDensity r k) fun n => by positivity

theorem turanDensity_le_one (r k : ℕ) : turanDensity r k ≤ 1 := by
  refine le_of_tendsto' (tendsto_turanDensity r k) fun n => ?_
  rcases Nat.eq_zero_or_pos (n.choose r) with h | h
  · simp [h]
  rw [div_le_one (by exact_mod_cast h)]
  exact_mod_cast ex_le_choose n r k

/-! ### The graph case `r = 2` (Turán's theorem) -/

/-- The `2`-uniform hypergraph (family of `2`-sets) of edges of a simple graph. -/
def edgeSets {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Finset (Finset (Fin n)) :=
  G.edgeFinset.image Sym2.toFinset

lemma toFinset_injective {α : Type*} [DecidableEq α] :
    Function.Injective (Sym2.toFinset (α := α)) := by
  intro z w h
  ext a
  rw [← Sym2.mem_toFinset, h, Sym2.mem_toFinset]

section edgeSets

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

lemma card_edgeSets : #(edgeSets G) = #G.edgeFinset :=
  card_image_of_injective _ toFinset_injective

lemma pair_mem_edgeSets {a b : Fin n} : ({a, b} : Finset (Fin n)) ∈ edgeSets G ↔ G.Adj a b := by
  rw [edgeSets, ← Sym2.toFinset_mk_eq, toFinset_injective.mem_finset_image]
  simp

lemma card_of_mem_edgeSets {e : Finset (Fin n)} (he : e ∈ edgeSets G) : e.card = 2 := by
  obtain ⟨z, hz, rfl⟩ := mem_image.1 he
  exact Sym2.card_toFinset_of_not_isDiag z (G.not_isDiag_of_mem_edgeSet (by simpa using hz))

lemma powersetCard_two_subset_edgeSets_iff (S : Finset (Fin n)) :
    S.powersetCard 2 ⊆ edgeSets G ↔ G.IsClique (S : Set (Fin n)) := by
  constructor
  · intro h a ha b hb hab
    rw [← pair_mem_edgeSets]
    apply h
    rw [mem_powersetCard, card_pair hab]
    refine ⟨?_, rfl⟩
    intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
  · intro h T hT
    rw [mem_powersetCard, card_eq_two] at hT
    obtain ⟨hTS, a, b, hab, rfl⟩ := hT
    rw [pair_mem_edgeSets]
    exact h (hTS (by simp)) (hTS (by simp)) hab

lemma isAdmissible_edgeSets {k : ℕ} (hG : G.CliqueFree k) : IsAdmissible n 2 k (edgeSets G) := by
  refine ⟨fun e he => card_of_mem_edgeSets G he, fun S hS hsub => ?_⟩
  rw [powersetCard_two_subset_edgeSets_iff] at hsub
  exact hG S ⟨hsub, hS⟩

end edgeSets

lemma exists_graph_of_isAdmissible {n k : ℕ} {H : Finset (Finset (Fin n))}
    (hH : IsAdmissible n 2 k H) :
    ∃ G : SimpleGraph (Fin n), ∃ _ : DecidableRel G.Adj, G.CliqueFree k ∧ edgeSets G = H := by
  classical
  let G := SimpleGraph.fromRel (fun a b : Fin n => ({a, b} : Finset (Fin n)) ∈ H)
  have hG : edgeSets G = H := by
    ext e
    constructor
    · intro he
      obtain ⟨a, b, hab, rfl⟩ := card_eq_two.1 (card_of_mem_edgeSets G he)
      rw [pair_mem_edgeSets] at he
      simp only [G, SimpleGraph.fromRel_adj] at he
      rcases he.2 with h | h
      · exact h
      · rwa [pair_comm]
    · intro he
      obtain ⟨a, b, hab, rfl⟩ := card_eq_two.1 (hH.1 e he)
      rw [pair_mem_edgeSets]
      simp only [G, SimpleGraph.fromRel_adj]
      exact ⟨hab, Or.inl he⟩
  refine ⟨G, inferInstance, fun S hS => ?_, hG⟩
  apply hH.2 S hS.2
  rw [← hG, powersetCard_two_subset_edgeSets_iff]
  exact hS.1

/-- For `r = 2` the extremal number is the number of edges of the Turán graph `T(n, k-1)`. -/
lemma ex_two_eq (n k : ℕ) (hk : 2 ≤ k) :
    ex n 2 k = #(SimpleGraph.turanGraph n (k - 1)).edgeFinset := by
  classical
  have hk' : k - 1 + 1 = k := by omega
  have hmax := SimpleGraph.isTuranMaximal_turanGraph (n := n) (r := k - 1) (by omega)
  apply le_antisymm
  · unfold ex
    refine Finset.sup_le fun H hH => ?_
    obtain ⟨G, _, hGf, rfl⟩ := exists_graph_of_isAdmissible (mem_filter.1 hH).2
    rw [card_edgeSets]
    exact hmax.2 (hk' ▸ hGf)
  · have hT := SimpleGraph.turanGraph_cliqueFree (n := n) (r := k - 1) (by omega)
    rw [hk'] at hT
    rw [← card_edgeSets]
    exact card_le_ex (isAdmissible_edgeSets _ hT)

/-- A residue class modulo `m` in `Fin n` has at most `n / m + 1` elements. -/
lemma card_residue_le (n m c : ℕ) :
    #(univ.filter fun w : Fin n => (w : ℕ) % m = c) ≤ n / m + 1 := by
  calc #(univ.filter fun w : Fin n => (w : ℕ) % m = c) ≤ #(range (n / m + 1)) := by
        apply Finset.card_le_card_of_injOn (fun w : Fin n => (w : ℕ) / m)
        · intro w _
          simpa using Nat.lt_succ_of_le (Nat.div_le_div_right (c := m) w.isLt.le)
        · intro w hw w' hw' h
          simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hw hw'
          apply Fin.ext
          rw [← Nat.div_add_mod (w : ℕ) m, ← Nat.div_add_mod (w' : ℕ) m, hw, hw']
          simp only at h
          rw [h]
    _ = n / m + 1 := card_range _

/-- A residue class `c < m` modulo `m` in `Fin n` has at least `n / m` elements. -/
lemma le_card_residue (n m c : ℕ) (hc : c < m) :
    n / m ≤ #(univ.filter fun w : Fin n => (w : ℕ) % m = c) := by
  rcases n with _ | n
  · simp
  have hval : ∀ j ∈ range ((n + 1) / m), (j * m + c) % (n + 1) = j * m + c := by
    intro j hj
    rw [mem_range] at hj
    rw [Nat.mod_eq_of_lt]
    have h1 : (j + 1) * m ≤ (n + 1) / m * m := Nat.mul_le_mul_right _ hj
    have h2 := Nat.div_mul_le_self (n + 1) m
    nlinarith
  calc (n + 1) / m = #(range ((n + 1) / m)) := (card_range _).symm
    _ ≤ _ := by
        apply Finset.card_le_card_of_injOn
          (fun j : ℕ => (⟨(j * m + c) % (n + 1), Nat.mod_lt _ n.succ_pos⟩ : Fin (n + 1)))
        · intro j hj
          have hj' : j ∈ range ((n + 1) / m) := by simpa using hj
          simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq]
          rw [hval j hj', Nat.mul_add_mod_of_lt hc]
        · intro j hj j' hj' h
          have hj1 : j ∈ range ((n + 1) / m) := by simpa using hj
          have hj2 : j' ∈ range ((n + 1) / m) := by simpa using hj'
          have := congrArg Fin.val h
          simp only at this
          rw [hval j hj1, hval j' hj2] at this
          have hm : 0 < m := by omega
          have : j * m = j' * m := by omega
          exact Nat.eq_of_mul_eq_mul_right hm this

/-- The degree of a vertex `v` of the Turán graph `T(n, m)` is `n` minus the size of the residue
class of `v` modulo `m`. -/
lemma turanGraph_degree_add (n m : ℕ) (v : Fin n) :
    (SimpleGraph.turanGraph n m).degree v +
      #(univ.filter fun w : Fin n => (w : ℕ) % m = v % m) = n := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have : (SimpleGraph.turanGraph n m).neighborFinset v =
      univ.filter fun w : Fin n => ¬ ((w : ℕ) % m = v % m) := by
    ext w
    simp [SimpleGraph.turanGraph_adj, eq_comm]
  rw [this, add_comm, Finset.card_filter_add_card_filter_not]
  simp

/-- Two-sided bounds on the number of edges of the Turán graph `T(n, m)`. -/
lemma turanGraph_edge_bounds (n m : ℕ) (hm : 0 < m) :
    (n : ℝ) * (n - n / m - 1) ≤ 2 * (#(SimpleGraph.turanGraph n m).edgeFinset : ℝ) ∧
      2 * (#(SimpleGraph.turanGraph n m).edgeFinset : ℝ) ≤ n * (n - n / m + 1) := by
  have hsum := SimpleGraph.sum_degrees_eq_twice_card_edges (SimpleGraph.turanGraph n m)
  have hsumR : 2 * (#(SimpleGraph.turanGraph n m).edgeFinset : ℝ) =
      ∑ v, ((SimpleGraph.turanGraph n m).degree v : ℝ) := by
    exact_mod_cast hsum.symm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have e1 : ((n / m : ℕ) : ℝ) ≤ n / m := Nat.cast_div_le
  have e2 : (n : ℝ) / m - 1 ≤ ((n / m : ℕ) : ℝ) := by
    have hd : (n : ℝ) = m * ((n / m : ℕ) : ℝ) + ((n % m : ℕ) : ℝ) := by
      exact_mod_cast (Nat.div_add_mod n m).symm
    have hr : ((n % m : ℕ) : ℝ) < m := by exact_mod_cast Nat.mod_lt n hm
    rw [div_sub_one hmR.ne', div_le_iff₀ hmR]
    nlinarith
  have hdeg : ∀ v : Fin n, (n : ℝ) - n / m - 1 ≤ (SimpleGraph.turanGraph n m).degree v ∧
      ((SimpleGraph.turanGraph n m).degree v : ℝ) ≤ n - n / m + 1 := by
    intro v
    have h1 := turanGraph_degree_add n m v
    have h2 := card_residue_le n m (v % m)
    have h3 := le_card_residue n m (v % m) (Nat.mod_lt _ hm)
    have h1R : ((SimpleGraph.turanGraph n m).degree v : ℝ) +
        (#(univ.filter fun w : Fin n => (w : ℕ) % m = v % m) : ℝ) = n := by
      exact_mod_cast h1
    have h2R : (#(univ.filter fun w : Fin n => (w : ℕ) % m = v % m) : ℝ) ≤
        ((n / m : ℕ) : ℝ) + 1 := by exact_mod_cast h2
    have h3R : ((n / m : ℕ) : ℝ) ≤
        (#(univ.filter fun w : Fin n => (w : ℕ) % m = v % m) : ℝ) := by exact_mod_cast h3
    constructor <;> linarith
  rw [hsumR]
  constructor
  · calc (n : ℝ) * (n - n / m - 1) = ∑ _v : Fin n, ((n : ℝ) - n / m - 1) := by
          rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ _ := sum_le_sum fun v _ => (hdeg v).1
  · calc _ ≤ ∑ _v : Fin n, ((n : ℝ) - n / m + 1) := sum_le_sum fun v _ => (hdeg v).2
      _ = (n : ℝ) * (n - n / m + 1) := by
          rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

lemma tendsto_turan_div_sq (m : ℕ) (hm : 0 < m) :
    Tendsto (fun n : ℕ => (#(SimpleGraph.turanGraph n m).edgeFinset : ℝ) / (n : ℝ) ^ 2) atTop
      (𝓝 (((m : ℝ) - 1) / (2 * m))) := by
  set c : ℝ := ((m : ℝ) - 1) / (2 * m)
  have hinv : Tendsto (fun n : ℕ => 1 / (2 * (n : ℝ))) atTop (𝓝 0) := by
    have := tendsto_one_div_atTop_nhds_zero_nat.const_mul (1 / 2 : ℝ)
    rw [mul_zero] at this
    exact this.congr fun n => one_div_mul_one_div _ _
  have hlow : Tendsto (fun n : ℕ => c - 1 / (2 * (n : ℝ))) atTop (𝓝 c) := by
    simpa using tendsto_const_nhds.sub hinv
  have hupp : Tendsto (fun n : ℕ => c + 1 / (2 * (n : ℝ))) atTop (𝓝 c) := by
    simpa using tendsto_const_nhds.add hinv
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hb := (turanGraph_edge_bounds n m hm).1
    have e : c - 1 / (2 * (n : ℝ)) = ((n : ℝ) * (n - n / m - 1)) / 2 / (n : ℝ) ^ 2 := by
      simp only [c]; field_simp; try ring
    rw [e]
    gcongr
    linarith
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hb := (turanGraph_edge_bounds n m hm).2
    have e : c + 1 / (2 * (n : ℝ)) = ((n : ℝ) * (n - n / m + 1)) / 2 / (n : ℝ) ^ 2 := by
      simp only [c]; field_simp; try ring
    rw [e]
    gcongr
    linarith

lemma tendsto_choose_two_div_sq :
    Tendsto (fun n : ℕ => (n.choose 2 : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 (1 / 2)) := by
  have h : Tendsto (fun n : ℕ => (1 / 2 : ℝ) - (1 / 2) * (1 / (n : ℝ))) atTop (𝓝 (1 / 2)) := by
    simpa using tendsto_const_nhds.sub (tendsto_one_div_atTop_nhds_zero_nat.const_mul (1 / 2 : ℝ))
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [Nat.cast_choose_two]
  have : (n : ℝ) ≠ 0 := by positivity
  field_simp

/-- Turán's theorem, asymptotic form: `ex_2(n, K_k) / (n choose 2) → 1 - 1/(k-1)`. -/
theorem tendsto_ex_two_div_choose (k : ℕ) (hk : 2 ≤ k) :
    Tendsto (fun n : ℕ => (ex n 2 k : ℝ) / n.choose 2) atTop (𝓝 (1 - 1 / ((k : ℝ) - 1))) := by
  have hm : 0 < k - 1 := by omega
  have hc : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have h := (tendsto_turan_div_sq (k - 1) hm).div tendsto_choose_two_div_sq (by norm_num)
  have hval : ((((k - 1 : ℕ) : ℝ) - 1) / (2 * ((k - 1 : ℕ) : ℝ))) / (1 / 2) =
      1 - 1 / ((k : ℝ) - 1) := by
    rw [hc]
    have : (k : ℝ) - 1 ≠ 0 := by rw [← hc]; exact_mod_cast hm.ne'
    field_simp
  rw [hval] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [ex_two_eq n k hk]
  have : (n : ℝ) ^ 2 ≠ 0 := by positivity
  exact div_div_div_cancel_right₀ this _ _

/-- Turán: for `r = 2` the density is `π(K_k) = 1 - 1/(k-1)`. -/
theorem turanDensity_two (k : ℕ) (hk : 2 ≤ k) :
    turanDensity 2 k = 1 - 1 / ((k : ℝ) - 1) :=
  tendsto_nhds_unique (tendsto_turanDensity 2 k) (tendsto_ex_two_div_choose k hk)

/-- Turán, in the normalisation used on the problem page: `ex_2(n, K_k) / n^2 → ½ (1 - 1/(k-1))`. -/
theorem tendsto_ex_two_div_sq (k : ℕ) (hk : 2 ≤ k) :
    Tendsto (fun n : ℕ => (ex n 2 k : ℝ) / (n : ℝ) ^ 2) atTop
      (𝓝 ((1 / 2) * (1 - 1 / ((k : ℝ) - 1)))) := by
  have hm : 0 < k - 1 := by omega
  have hc : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have h := tendsto_turan_div_sq (k - 1) hm
  have hval : (((k - 1 : ℕ) : ℝ) - 1) / (2 * ((k - 1 : ℕ) : ℝ)) =
      (1 / 2) * (1 - 1 / ((k : ℝ) - 1)) := by
    rw [hc]
    have : (k : ℝ) - 1 ≠ 0 := by rw [← hc]; exact_mod_cast hm.ne'
    field_simp
  rw [hval] at h
  simpa only [ex_two_eq _ k hk] using h

/-! ### The problem statement -/

/-- **Erdős Problem #712.** A function `answer` *solves* the problem if, for every `k > r > 2`,
`ex_r(n, K_k^r) / (n choose r) → answer r k`. The problem asks for an explicit such `answer`. -/
def IsSolution (answer : ℕ → ℕ → ℝ) : Prop :=
  ∀ r k : ℕ, 2 < r → r < k →
    Tendsto (fun n => (ex n r k : ℝ) / n.choose r) atTop (𝓝 (answer r k))

/-- The limits in Erdős Problem #712 exist: `turanDensity` satisfies `IsSolution`, and any solution
coincides with it. The open problem is to find a closed form for `turanDensity r k`. -/
theorem isSolution_iff (answer : ℕ → ℕ → ℝ) :
    IsSolution answer ↔ ∀ r k : ℕ, 2 < r → r < k → answer r k = turanDensity r k := by
  constructor
  · intro h r k hr hk
    exact tendsto_nhds_unique (h r k hr hk) (tendsto_turanDensity r k)
  · intro h r k hr hk
    rw [h r k hr hk]
    exact tendsto_turanDensity r k

/-- Turán's conjecture (the special case `r = 3`, `k = 4`, Erdős Problem #500): the value
is `5/9`. This is stated here as a proposition only; it is open. -/
def TuranConjecture : Prop := turanDensity 3 4 = 5 / 9

end Erdos712
