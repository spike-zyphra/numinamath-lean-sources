import Mathlib

/-
Determine the sum of all positive integer values of $n$ for which $n^2 + 19n + 130$ is a perfect square.
-/

theorem algebra_620312 :
{n:ℕ | 0<n ∧ (IsSquare (n^2 + 19 * n + 130))} = {3,30} ∧ ∑x∈{3,30}, x = 33 := by
  
  let S := {n:ℕ | 0<n ∧ (IsSquare (n^2 + 19 * n + 130))}
  have hS : S = {3,30} := by 
    ext n
    constructor
    intro hn
    
    simp [S] at hn
    obtain ⟨npos, hn⟩ := hn
    obtain ⟨k,hk⟩ := hn
    simp

    have lb : (n+9)^2 < n^2 + 19 * n + 130 := by nlinarith
    have ub : n^2+19*n + 130 < (n+12)^2 := by nlinarith
    have lbk: (n+9) < k:= by nlinarith
    have ubk: k < n+12 := by nlinarith

    by_cases ke10 : k = n + 10
    rw [ke10] at hk
    rify at hk
    ring_nf at hk
    field_simp at hk
    have : (n:ℝ) = 30 := by linarith
    norm_cast at this
    right
    exact this
    by_cases ke11 : k = n + 11
    rw [ke11] at hk
    rify at hk
    ring_nf at hk
    field_simp at hk
    have : (n:ℝ) = 3 := by linarith
    norm_cast at this
    left
    exact this
    have ke12 : k = n + 12 := by omega
    omega

    intro hn
    simp at hn
    simp [S]
    rcases hn with hn | hn
    simp [hn]
    use 14
    simp [hn]
    use 40
    
    

  simp [S] at hS
  tauto
