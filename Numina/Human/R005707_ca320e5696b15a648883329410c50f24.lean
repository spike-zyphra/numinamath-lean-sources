import Mathlib

/-

-/
theorem Number_Theory_609507 :
    {(a, b) : ℤ × ℤ | a ∣ 720 ∧ b ∣ 720 ∧ ¬(a * b ∣ 720)}.ncard = 2520 := by

  -- h1: Restricts the infinite set of integer pairs to a finite set [-720, 720]×[-720, 720]. since any divisor of 720 must lie within this range.
  have h1 : {(a, b) : ℤ × ℤ | a ∣ 720 ∧ b ∣ 720 ∧ ¬(a * b ∣ 720)} = Finset.filter (fun p : ℤ × ℤ => (p.1 ∣ 720 ∧ p.2 ∣ 720 ∧ ¬(p.1 * p.2 ∣ 720))) (Finset.Icc (-720) 720 ×ˢ Finset.Icc (-720) 720) := by
    ext ⟨a, b⟩
    simp
    intro ha hb h

    -- Prove that a is at most 720
    have h2 : a ≤ 720 := by
      apply Int.le_of_dvd (by norm_num) ha

    -- Prove that a is at least -720
    have h3 : a ≥ -720 := by
      have h4 : (-a) ∣ 720 := by
        exact Int.neg_dvd.2 ha
      have h5 : -a ≤ 720 := by
        apply Int.le_of_dvd (by norm_num) h4
      omega

    -- Prove that b is at most 720
    have h6 : b ≤ 720 := by
      apply Int.le_of_dvd (by norm_num) hb
      
    -- Prove that b is at least -720
    have h7 : b ≥ -720 := by
      have h8 : (-b) ∣ 720 := by
        exact Int.neg_dvd.2 hb
      have h9 : -b ≤ 720 := by
        apply Int.le_of_dvd (by norm_num) h8
      omega
    omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide 