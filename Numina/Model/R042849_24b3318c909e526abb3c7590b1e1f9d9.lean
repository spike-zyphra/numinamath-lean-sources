import Mathlib

open Finset Real

theorem inequalities_158518 {n : ℕ} (hn : 0 < n) (a b : ℕ → ℝ)
    (ha : ∀ i ∈ Icc 1 n, 0 < a i) (hb : ∀ i ∈ Icc 1 n, 0 < b i)
    (h : a 1 ^ 2 > ∑ i ∈ Icc 2 n, (a i) ^ 2) :
    (∑ i ∈ Icc 1 n, (a i) ^ 2 - ∑ i ∈ Icc 2 n, (a i) ^ 2) *
    (∑ i ∈ Icc 1 n, (b i) ^ 2 - ∑ i ∈ Icc 2 n, (b i) ^ 2) ≤
    (∑ i ∈ Icc 1 n, (a i) * (b i) - ∑ i ∈ Icc 2 n, (a i) * (b i)) ^ 2 := by 
  have h1 : 1 ≤ n := by omega
  have h2 : 1 ∈ Icc 1 n := by 
    simp [Set.mem_Icc]
    all_goals omega
  have ha1 : 0 < a 1 := by 
    specialize ha 1 h2
    simpa using ha
  have hb1 : 0 < b 1 := by 
    specialize hb 1 h2
    simpa using hb
  have h1 : ∑ i ∈ Icc 1 n, (a i) ^ 2 = (a 1) ^ 2 + ∑ i ∈ Icc 2 n, (a i) ^ 2 := by
    have h3 : Icc 1 n = {1} ∪ Icc 2 n := by
      ext x
      simp at *
      omega
    rw [h3] 
    rw [Finset.sum_union, Finset.sum_singleton]
    <;> ring_nf <;> simp [Finset.sum_union, Finset.sum_singleton] <;> ring
  have h1' : ∑ i ∈ Icc 1 n, (b i) ^ 2 = (b 1) ^ 2 + ∑ i ∈ Icc 2 n, (b i) ^ 2 := by
    have h4 : Icc 1 n = {1} ∪ Icc 2 n := by
      ext x
      simp at *
      omega
    rw [h4]
    rw [Finset.sum_union, Finset.sum_singleton]
    <;> ring_nf <;> simp [Finset.sum_union, Finset.sum_singleton] <;> ring
  have h2 : ∑ i ∈ Icc 1 n, (a i) * (b i) = (a 1) * (b 1) + ∑ i ∈ Icc 2 n, (a i) * (b i) := by
    have h5 : Icc 1 n = {1} ∪ Icc 2 n := by
      ext x
      simp at *
      omega
    rw [h5]
    rw [Finset.sum_union, Finset.sum_singleton]
    <;> ring_nf <;> simp [Finset.sum_union, Finset.sum_singleton] <;> ring
  rw [h1]
  rw [h1']
  rw [h2]
  have ha2 := ha 1 (by simp [Set.mem_Icc] at *; all_goals omega)
  have hb2 := hb 1 (by simp [Set.mem_Icc] at *; all_goals omega)
  nlinarith [mul_pos ha1 hb1, mul_pos ha1 (show 0 < b 1 by apply hb 1; simp [Set.mem_Icc] at *; all_goals omega), 
          mul_pos (show 0 < a 1 by apply ha 1; simp [Set.mem_Icc] at *; all_goals omega) hb1,
          mul_nonneg (show 0 ≤ a 1 ^ 2 by positivity) (show 0 ≤ b 1 ^ 2 by positivity), 
          mul_nonneg (show 0 ≤ a 1 ^ 2 by positivity) (show 0 ≤ ∑ i ∈ Icc 2 n, (b i) ^ 2 by positivity), 
          mul_nonneg (show 0 ≤ b 1 ^ 2 by positivity) (show 0 ≤ ∑ i ∈ Icc 2 n, (a i) ^ 2 by positivity), 
          mul_nonneg (show 0 ≤ ∑ i ∈ Icc 2 n, (a i) ^ 2 by positivity) (show 0 ≤ ∑ i ∈ Icc 2 n, (b i) ^ 2 by positivity)
         ]