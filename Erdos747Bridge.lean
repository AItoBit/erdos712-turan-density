/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license.

Bridge to the proof by plby/lean-proofs, commit
8822f7ddef30fadbd92e1c6ab4ed897af356af5e.
The imported proof follows Jeff Kahn, Asymptotics for Shamir's Problem.
-/
import ErdosProblems.Erdos747
import FormalConjecturesUtil

open Filter
open scoped Topology

namespace Erdos747Bridge

lemma probability_eq (n m : ℕ) :
    Hypergraph.matchingProbability (3 * n) 3 m n =
      Erdos747.pmProbability n m := by
  classical
  have hevent (H : Finset (Finset (Fin (3 * n)))) :
      H.HasHypergraphMatching n ↔ Erdos747.HasPerfectMatching n H := by
    rfl
  have hfilter :
      ((Hypergraph.fixedSizeFamilies (3 * n) 3 m).filter
        (fun H ↦ H.HasHypergraphMatching n)) = Erdos747.goodSample n m := by
    change ((Erdos747.sample n m).filter
      (fun H ↦ H.HasHypergraphMatching n)) =
        (Erdos747.sample n m).filter (Erdos747.HasPerfectMatching n)
    apply Finset.filter_congr
    intro H hH
    exact hevent H
  unfold Hypergraph.matchingProbability Erdos747.pmProbability
  rw [hfilter]
  rfl

lemma log_normalization (n : ℕ) (hn : 1 ≤ n) :
    Real.log (3 * (n : ℝ)) = Real.log 3 + Real.log (n : ℝ) := by
  exact Real.log_mul (by norm_num) (by exact_mod_cast (show n ≠ 0 by omega))

/-- The exact two-sided statement currently used by Formal Conjectures #747. -/
theorem exact_threshold :
    ∀ ε : ℝ, 0 < ε → ε < 1 →
    Tendsto (fun n ↦ Hypergraph.matchingProbability (3 * n) 3
      ⌊(1 + ε) * ((n : ℝ) * Real.log n)⌋₊ n) atTop (𝓝 1) ∧
    Tendsto (fun n ↦ Hypergraph.matchingProbability (3 * n) 3
      ⌊(1 - ε) * ((n : ℝ) * Real.log n)⌋₊ n) atTop (𝓝 0) := by
  intro ε hε hε1
  have hδ : 0 < ε / 2 := by positivity
  have hδ1 : ε / 2 < 1 := by linarith
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hloglim : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hupper : ∀ᶠ n : ℕ in atTop,
      Erdos747.upperEdgeCount (ε / 2) n ≤
        ⌊(1 + ε) * ((n : ℝ) * Real.log n)⌋₊ := by
    filter_upwards [eventually_ge_atTop 1,
      hloglim.eventually_ge_atTop
        (2 * ((1 + ε / 2) * Real.log 3 + 1) / ε)] with n hn hl
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hslack : (1 + ε / 2) * Real.log 3 + 1 ≤
        (ε / 2) * Real.log (n : ℝ) := by
      have hmul := (div_le_iff₀ hε).mp hl
      nlinarith
    have hgap :
        (1 + ε / 2) * Erdos747.shamirScale n + 1 ≤
          (1 + ε) * ((n : ℝ) * Real.log n) := by
      unfold Erdos747.shamirScale
      rw [log_normalization n hn]
      have hscaled := mul_le_mul_of_nonneg_left hslack (by positivity : (0 : ℝ) ≤ n)
      nlinarith
    apply Nat.ceil_le.mpr
    have hf := Nat.lt_floor_add_one ((1 + ε) * ((n : ℝ) * Real.log n))
    change (1 + ε / 2) * Erdos747.shamirScale n ≤ _
    linarith
  have hlower : ∀ᶠ n : ℕ in atTop,
      ⌊(1 - ε) * ((n : ℝ) * Real.log n)⌋₊ ≤
        Erdos747.lowerEdgeCount (ε / 2) n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    apply Nat.floor_mono
    unfold Erdos747.shamirScale
    rw [log_normalization n hn]
    have hln : 0 ≤ Real.log (n : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hn)
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have hdiff : 0 ≤ ε / 2 * Real.log (n : ℝ) +
        (1 - ε / 2) * Real.log 3 :=
      add_nonneg (mul_nonneg hδ.le hln) (mul_nonneg (by linarith) hlog3)
    have := mul_nonneg hn0 hdiff
    nlinarith
  have hvalid : ∀ᶠ n : ℕ in atTop,
      ⌊(1 + ε) * ((n : ℝ) * Real.log n)⌋₊ ≤ (Erdos747.allEdges n).card := by
    filter_upwards [Erdos747.eventually_upperEdgeCount_le_card ε hε.le,
      eventually_ge_atTop 1] with n hn hn1
    apply le_trans _ hn
    apply le_trans (Nat.floor_le_ceil _)
    apply Nat.ceil_mono
    unfold Erdos747.shamirScale
    rw [log_normalization n hn1]
    have := mul_nonneg (by positivity : (0 : ℝ) ≤ (1 + ε) * n) hlog3
    nlinarith
  constructor
  · have hlim := Erdos747.upper_pmProbability_tendsto_one (ε / 2) hδ
    have : Tendsto (fun n ↦ Erdos747.pmProbability n
        ⌊(1 + ε) * ((n : ℝ) * Real.log n)⌋₊) atTop (𝓝 1) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds
      · filter_upwards [hupper, hvalid] with n hn hv
        exact Erdos747.pmProbability_mono_of_le hn hv
      · exact Eventually.of_forall fun n ↦ Erdos747.pmProbability_le_one n _
    simpa only [probability_eq] using this
  · have hlim := Erdos747.lower_pmProbability_tendsto_zero (ε / 2) hδ hδ1
    have : Tendsto (fun n ↦ Erdos747.pmProbability n
        ⌊(1 - ε) * ((n : ℝ) * Real.log n)⌋₊) atTop (𝓝 0) := by
      apply squeeze_zero' (Eventually.of_forall fun n ↦ Erdos747.pmProbability_nonneg n _) _ hlim
      filter_upwards [hlower, Erdos747.eventually_upperEdgeCount_le_card 0 (by norm_num)]
        with n hn hv
      apply Erdos747.pmProbability_mono_of_le hn
      exact (Erdos747.lowerEdgeCount_le_upper_zero (ε / 2) hδ.le hδ1.le n).trans hv
    simpa only [probability_eq] using this

end Erdos747Bridge
