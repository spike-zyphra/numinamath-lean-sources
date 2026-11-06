import Mathlib

/-What is the smallest positive integer that cannot be written as the sum of two nonnegative palindromic integers? (An integer is palindromic if the sequence of decimal digits are the same when read backwards.)-/

def Is_palindromic (n : ℕ) : Prop := n ≤ 9 ∨ ∃ m: ℕ, n = 11 * m

theorem number_theory_609943: IsLeast {n: ℕ | ¬ ∃ a b: ℕ, Is_palindromic a ∧ Is_palindromic b ∧ n = a + b} 21 := by
  constructor
  -- show that 21 is in the set
  . simp only [Set.mem_setOf_eq]
    by_contra! h
    obtain ⟨a, b, ha, hb, h⟩ := h
    by_cases hab: a ≤ b
    -- the case a ≤ b
    . have lb: 11 ≤ b := by linarith
      simp [Is_palindromic] at hb
      have o: ¬ b ≤ 9 := by omega
      simp [o] at hb
      obtain ⟨m, hb⟩ := hb
      have lb2: b ≤ 21 := by linarith
      have hm: m = 1 := by linarith
      simp [hm] at hb
      simp [hb] at h
      simp [Is_palindromic,h] at ha
      omega
    -- the case a > b
    . have la: 11 ≤ a := by linarith
      simp [Is_palindromic] at ha
      have o: ¬ a ≤ 9 := by omega
      simp [o] at ha
      obtain ⟨m, ha⟩ := ha
      have la2: a ≤ 21 := by linarith
      have hm: m = 1 := by linarith
      simp [hm] at ha
      simp [ha] at h
      simp [Is_palindromic,h] at hb
      omega

  -- show that 21 is the least element
  . intro n h
    simp only [Set.mem_setOf_eq] at h
    by_contra! hn
    absurd h
    clear h
    by_cases ln: n ≤ 9
    -- the case n ≤ 9
    . use 0
      use n
      simp [Is_palindromic]
      left
      omega
    -- the case n > 9
    . by_cases ln2: n ≤ 18
      -- the case n ≤ 18
      . use 9
        use n - 9
        simp [Is_palindromic]
        constructor
        . simp [ln2]
        . omega
      -- the case n > 18
      . simp at ln2
        clear ln
        use 11
        use n - 11
        simp [Is_palindromic]
        omega