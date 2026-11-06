import Mathlib

theorem algebra_11948 {f : ℤ → ℤ}
    (hf : ∀ n, Odd n → f n = n + 3)
    (hf' : ∀ n, Even n → f n = n / 2)
    (k : ℤ) (hk : Odd k) (h : f (f (f k)) = 27) :
    k = 105 := by
  have h1 : f k = k + 3 := by
    apply hf k hk
  have h2 : k % 2 = 1 := by
    obtain ⟨m, hm⟩ := hk
    omega
  have h3 : (k + 3) % 2 = 0 := by 
    omega
  have h4 : f (f k) = (k + 3) / 2 := by 
    rw [h1]
    have h5 : Even (k + 3) := by 
      exact ⟨(k + 3) / 2, by omega⟩
    apply hf' (k + 3) h5
  have eq1 : f (f (f k)) = f ((k + 3) / 2) := by 
    rw [h4]
  rw [eq1] at h
  by_cases h7 : Even ((k + 3) / 2)
  · -- Assume (k + 3)/2 is even
    have h8 : f ((k + 3) / 2) = ((k + 3) / 2) / 2 := by
      apply hf' ((k + 3) / 2) h7
    have h9 : (k + 3) / 2 = 54 := by 
      rw [h8] at h
      have h10 : ((k + 3) / 2) % 2 = 0 := by
        obtain ⟨m, hm⟩ := h7
        omega
      omega
    have h10 : k = 105 := by 
      omega
    exact_mod_cast h10
  · -- Assume (k + 3)/2 is odd
    have h9 : Odd ((k + 3) / 2) := by
      simpa using h7
    have h10 : f ((k + 3) / 2) = ((k + 3) / 2) + 3 := by
      apply hf ((k + 3) / 2) h9
    have eq2 : (k + 3) / 2 = 24 := by 
      rw [h10] at h 
      omega
    have h11 : k = 45 := by 
      omega
    have eq3 : f (f (f k)) = 12 := by
      rw [show k = 45 by omega]
      norm_num [hf, hf', show Odd (45 : ℤ) by decide, show Even (48 : ℤ) by decide, show Even (24 : ℤ) by decide]
    linarith [eq3, h]