import Mathlib

theorem number_theory_315792 (a : ℕ → ℤ) (ha : ∀ n ∈ Finset.Icc 1 1986, a n = 1 ∨ a n = -1) :
    Odd (∑ i ∈ Finset.Icc 1 1986, a i * i) := by
  have h1 : (∑ i in Finset.Icc 1 1986, a i * i) % 2 = 1 := by
    have h2 : ∀ i ∈ Finset.Icc 1 1986, a i % 2 = 1 := by
      intro i hi
      have h3 : a i = 1 ∨ a i = -1 := ha i hi
      rcases h3 with (h | h)
      · omega
      · omega
    have h4 : (∑ i in Finset.Icc 1 1986, a i * i) % 2 = 1 := by
      have h5 : (∑ i in Finset.Icc 1 1986, a i * i) % 2 = (∑ i in Finset.Icc 1 1986, (a i * i) % 2) % 2 := by
        simp [Finset.sum_int_mod]
      rw [h5]
      have h8 : (∑ i in Finset.Icc 1 1986, (a i * i) % 2) % 2 = 1 := by
        have h9 : (∑ i in Finset.Icc 1 1986, (a i * i) % 2) = 993 := by
          have h10 : ∀ i ∈ Finset.Icc 1 1986, (a i * i : ℤ) % 2 = if Odd i then 1 else 0 := by
            intro i hi
            have h20 : a i % 2 = 1 := h2 i hi
            have h30 : (i : ℤ) % 2 = 1 ∨ (i : ℤ) % 2 = 0 := by omega
            have h50 : (a i * i : ℤ) % 2 = if Odd i then 1 else 0 := by
              rcases h30 with (h30 | h30)
              · -- i is odd
                have h14 : Odd i := by
                  refine' ⟨(i - 1) / 2, by omega⟩
                simp [h14]
                have h11 : a i % 2 = 1 := h20
                have h12 : (i : ℤ) % 2 = 1 := by omega
                have h13 : (a i * (i : ℤ)) % 2 = 1 := by
                  simp [Int.mul_emod, h11, h12]
                omega
              · -- i is even
                have h14 : ¬ Odd i := by
                  intro h
                  obtain ⟨k, hk⟩ := h
                  omega
                simp [h14]
                have h11 : a i % 2 = 1 := h20
                have h12 : (i : ℤ) % 2 = 0 := by omega
                have h13 : (a i * (i : ℤ)) % 2 = 0 := by
                  simp [Int.mul_emod, h11, h12]
                omega
            exact h50
          have h11 : (∑ i in Finset.Icc 1 1986, (a i * i : ℤ) % 2) = (∑ i in Finset.Icc 1 1986, (if Odd i then 1 else 0 : ℤ)) := by
            apply Finset.sum_congr
            · rfl
            intro i hi
            have h7 : (a i * i : ℤ) % 2 = if Odd i then 1 else 0 := h10 i hi
            simpa [h7]
          rw [h11]
          native_decide
        omega
      omega
    exact h4
  have h7 : (∑ i in Finset.Icc 1 1986, a i * i) % 2 = 1 := h1
  exact ⟨(∑ i in Finset.Icc 1 1986, a i * i) / 2, by omega⟩