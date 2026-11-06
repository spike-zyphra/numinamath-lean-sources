import Mathlib

--Use the Chinese remainder theorem.
lemma l1 (n:ℤ):
n % 3 = 1 ∧ n % 5 = 3 ∧ n % 7 = 5 ↔ n % 105 = 103 := by
  omega

theorem number_theory_638482 (L0: ℤ) (L0pos : 0 < L0):
IsLeast {N : ℤ  | L0 < N ∧ N % 3 = 1 ∧ N % 5 = 3 ∧ N % 7 = 5} (105 * (⌊(L0+2)/(105:ℝ)⌋+1)-2)  := by 
  
  unfold IsLeast lowerBounds
  simp [l1]

  constructor
  
  --It is valid by simple calculation.
  constructor
  rify
  have : (↑L0 + 2) / 105  < @HAdd.hAdd ℝ ℝ ℝ instHAdd (↑⌊((L0:ℝ) + 2) / 105⌋) 1 := by
    exact Int.lt_floor_add_one (((L0:ℝ) + 2) / 105) 
  linarith
  omega

  -- It is the least one.
  intro r L0lr hm
  have t1 : 105 ∣ r - 103 := by 
    exact Int.dvd_sub_of_emod_eq hm
  --We have r = 105 * d + 103.
  obtain ⟨d, hd⟩ := t1
  have t2 : r = 105 * d + 103 := by omega
  --We verfiy that d has to be large.
  have t3 : ⌊((L0:ℝ) + 2) / 105⌋ ≤ d := by 
    by_contra ll
    push_neg at ll
    have : d ≤ ⌊((L0:ℝ) + 2) / 105⌋ - 1 := by linarith
    have l1: 105*d + 103 ≤ 105 * (⌊((L0:ℝ) + 2) / 105⌋ - 1) + 103 := by linarith
    rw [← t2] at l1
    have : 105 * (⌊((L0:ℝ) + 2) / 105⌋ - 1) + 103 ≤ L0 := by 
      have l2 : ⌊((L0:ℝ) + 2) / 105⌋ ≤ ((L0:ℝ) + 2) / 105 := by exact Int.floor_le (((L0:ℝ) + 2) / 105)
      have l3: 105 * (⌊((L0:ℝ) + 2) / 105⌋ - 1) + 103 ≤ 105 * (((L0:ℝ) + 2) / 105 - 1) + 103 := by linarith
      have l4: 105 * (((L0:ℝ) + 2) / 105 - 1) + 103 = L0 := by ring
      rify
      linarith
    linarith
  nlinarith
