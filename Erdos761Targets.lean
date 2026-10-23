/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import FormalConjecturesUtil

/-!
# Erdős Problem 761

*References:*
- [erdosproblems.com/761](https://www.erdosproblems.com/761)
- [ErGi93] Erdős, P. and Gimbel, J., *Some problems and results in cochromatic theory*.
  Quo vadis, graph theory? (1993), 261-264.
-/


universe u

namespace Erdos761

/-- The vertices in `S` span no directed cycle of `D`: there is no closed directed walk of
positive length inside `S`. -/
def IsAcyclicOn {V : Type*} (D : Digraph V) (S : Set V) : Prop :=
  ∀ v : V, ¬ Relation.TransGen (fun a b : V ↦ a ∈ S ∧ b ∈ S ∧ D.Adj a b) v v

/-- `Dicolorable G k` says that, for every orientation `D` of `G`, the vertices can be coloured
with `k` colours such that no colour class contains a directed cycle of `D`. -/
def Dicolorable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ D : Digraph V, D.IsOrientation G →
    ∃ c : V → Fin k, ∀ i : Fin k, IsAcyclicOn D {v | c v = i}

/-- The dichromatic number $\delta(G)$: the least `k` such that `G` is `k`-dicolorable. It is
finite for finite graphs, since colouring all vertices differently works. -/
noncomputable def dichromaticNumber {V : Type*} (G : SimpleGraph V) : ℕ∞ :=
  ⨅ (k : ℕ) (_ : Dicolorable G k), (k : ℕ∞)

/-- If `Dicolorable G k` holds, then $\delta(G) \leq k$. -/
theorem dichromaticNumber_le {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (h : Dicolorable G k) : dichromaticNumber G ≤ k :=
  iInf₂_le k h

/-- The open chromatic-to-dichromatic question, stated without claiming a proof. -/
def FirstQuestion : Prop :=
  ∀ k : ℕ, ∃ m : ℕ, ∀ (V : Type*) [Finite V] (G : SimpleGraph V),
    (m : ℕ∞) ≤ G.chromaticNumber → (k : ℕ∞) ≤ dichromaticNumber G

/-- The open cochromatic/subgraph question, stated without claiming a proof. -/
def SecondQuestion : Prop :=
  ∀ k : ℕ, ∃ m : ℕ, ∀ (V : Type*) [Finite V] (G : SimpleGraph V),
    (m : ℕ∞) ≤ G.cochromaticNumber →
      ∃ H : G.Subgraph, (k : ℕ∞) ≤ dichromaticNumber H.coe

end Erdos761


