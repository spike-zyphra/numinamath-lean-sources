import Mathlib

theorem number_theory_234205 (a b : ℕ) (ha : 2 < a) (hb : 2 < b) :
    ∃ k > 0, ∃ n : ℕ → ℕ,
      n 0 = a ∧
      n (k - 1) = b ∧
      ∀ i ∈ Finset.Icc 0 (k - 2), (n i + n (i + 1)) ∣ n i * n (i + 1) := by
  use 3
  constructor
  · norm_num
  use fun i =>
    match i with
    | 0 => a
    | 1 => 0
    | 2 => b
    | _ => 0
  constructor
  · rfl
  constructor
  · rfl
  · intro i hi
    fin_cases hi <;> simp [Finset.mem_Icc]
    <;> omega