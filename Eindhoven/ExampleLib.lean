import Mathlib.Topology.MetricSpace.Basic
import Verbose.English.All

def continuous_function_at (f : ℝ → ℝ) (x₀ : ℝ) :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

def sequence_tendsto (u : ℕ → ℝ) (l : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

notation:50 f:80 " is continuous at " x₀ => continuous_function_at f x₀
notation:50 u:80 " converges to " l => sequence_tendsto u l

def is_supremum (M : ℝ) (u : ℕ → ℝ) :=
(∀ n, u n ≤ M) ∧ ∀ ε > 0, ∃ n₀, u n₀ ≥ M - ε


section Subset
variable {α : Type*}

/- The Mathlib definition of `Set.Subset` uses a strict-implicit
argument which confuses Verbose Lean. So let us replace it. -/

protected def Verbose.English.Subset (s₁ s₂ : Set α) :=
  ∀ x, x ∈ s₁ → x ∈ s₂

instance (priority := high) Verbose.English.hasSubset : HasSubset (Set α) :=
  ⟨Verbose.English.Subset⟩

end Subset

def pair (n : ℤ) := ∃ k, n = 2*k
notation:50 n:70 " is even" => pair n

def impair (n : ℤ) := ∃ k, n = 2*k + 1
notation:50 n:70 " is odd" => impair n

lemma non_pair_et_impair (n : ℤ) : ¬ (n is even ∧ n is odd) := by
  rintro ⟨⟨k, rfl⟩, ⟨l, h⟩⟩
  omega

lemma non_pair_impair (n : ℤ) (h : n is even) (h' : n is odd) : False :=
  non_pair_et_impair n ⟨h, h'⟩

lemma pair_iff_even (n : ℤ) : n is even ↔ Even n := by
  apply exists_congr (fun k ↦ ?_)
  rw [Int.two_mul]

lemma impair_iff_odd (n : ℤ) : n is odd ↔ Odd n := Iff.rfl

@[push_neg_extra]
lemma non_pair_ssi_impair (n : ℤ) : ¬ n is even ↔ n is odd := by
  simp [pair_iff_even, impair_iff_odd]

@[push_neg_extra]
lemma non_impair_ssi_pair (n : ℤ) : ¬ n is odd ↔ n is even := by
  simp [pair_iff_even, impair_iff_odd]

-- Les deux lemmes suivants sont nécéssaires si `sufficesPushNeg` a déplié la
-- définition de pair ou impair

@[push_neg_extra]
lemma non_pair_ssi_impair' (n : ℤ) : (∀ k, n ≠ 2*k) ↔ n is odd := by
  rw [← non_pair_ssi_impair, «pair», not_exists]

@[push_neg_extra]
lemma non_impair_ssi_pair' (n : ℤ) : (∀ k, n ≠ 2*k + 1) ↔ n is even := by
  rw [← non_impair_ssi_pair, «impair», not_exists]

lemma impair_car_non_pair (n : ℤ) (h : ¬ n is even) : n is odd :=
  (non_pair_ssi_impair n).1 h

lemma pair_car_non_impair (n : ℤ) (h : ¬ n is odd) : n is even :=
  (non_impair_ssi_pair n).1 h

lemma non_pair_car_impair (n : ℤ) (h : n is odd) : ¬ n is even :=
  (non_pair_ssi_impair n).2 h

lemma non_impair_car_pair (n : ℤ) (h : n is even) : ¬ n is odd :=
  (non_impair_ssi_pair n).2 h
open Verbose.English

lemma le_of_abs_le' {α : Type*} [LinearOrderedAddCommGroup α] {x y : α} : |x| ≤ y → -y ≤ x := fun h ↦ abs_le.1 h |>.1

configureAnonymousFactSplittingLemmas le_le_of_abs_le le_le_of_max_le le_of_max_le_left le_of_max_le_right le_of_abs_le le_of_abs_le'

configureAnonymousGoalSplittingLemmas LogicIntros AbsIntros Set.Subset.antisymm

useDefaultDataProviders

useDefaultSuggestionProviders

configureUnfoldableDefs continuous_function_at sequence_tendsto pair impair
