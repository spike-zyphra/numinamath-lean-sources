import Mathlib

theorem number_theory_2749 : ¬∃ x, x ^ 2014 ≡ 2 [ZMOD 19] := by
  rintro ⟨x, hx⟩
  have h1 : x ^ 2014 % 19 = 2 := hx
  have h2 : x % 19 = 0 ∨ x % 19 = 1 ∨ x % 19 = 2 ∨ x % 19 = 3 ∨ x % 19 = 4 ∨ x % 19 = 5 ∨ x % 19 = 6 ∨ x % 19 = 7 ∨ x % 19 = 8 ∨ x % 19 = 9 ∨ x % 19 = 10 ∨ x % 19 = 11 ∨ x % 19 = 12 ∨ x % 19 = 13 ∨ x % 19 = 14 ∨ x % 19 = 15 ∨ x % 19 = 16 ∨ x % 19 = 17 ∨ x % 19 = 18 := by 
    omega
  have h1' : (x % 19) ^ 2014 % 19 = 2 := by
    have h4 : (x : ℤ) ^ 2014 % 19 = (x % 19) ^ 2014 % 19 := by
      have h6 : ∀ (n : ℕ), (x ^ n : ℤ) % 19 = (x % 19) ^ n % 19 := by
        intro n
        induction n with
        | zero =>
          simp 
        | succ n ih =>
          simp [pow_succ, Int.mul_emod, Int.add_emod, Int.sub_emod, ih]
          <;> try ring_nf 
          <;> try norm_num 
          <;> try omega
      specialize h6 2014
      simpa using h6
    omega 
  rcases h2 with (h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h)
  · -- case x % 19 = 0 
    rw [h] at h1' 
    norm_num at h1' 
  · -- case x % 19 = 1 
    rw [h] at h1' 
    norm_num at h1' 
  · -- case x % 19 = 2 
    rw [h] at h1' 
    norm_num at h1' 
  · -- case x % 19 = 3 
    rw [h] at h1' 
    norm_num at h1' 
  · -- case x % 19 = 4 
    rw [h] at h1' 
    norm_num at h1' 
  · -- case x % 19 = 5 
    rw [h] at h1' 
    norm_num at h1' 
  · -- case x % 19 = 6 
    rw [h] at h1' 
    norm_num at h1' 
  · -- case x % 19 = 7 
    rw [h] at h1' 
    norm_num at h1' 
  · -- case x % 19 = 8 
    rw [h] at h1' 
    norm_num at h1' 
  · -- case x % 19 = 9 
    rw [h] at h1' 
    norm_num at h1' 
  · -- case x % 19 = 10 
    rw [h] at h1' 
    norm_num at h1' 
  · -- case x % 19 = 11 
    rw [h] at h1' 
    norm_num at h1' 
  · -- case x % 19 = 12 
    rw [h] at h1' 
    norm_num at h1' 
  · -- case x % 19 = 13 
    rw [h] at h1' 
    norm_num at h1' 
  · -- case x % 19 = 14 
    rw [h] at h1' 
    norm_num at h1' 
  · -- case x % 19 = 15 
    rw [h] at h1' 
    norm_num at h1' 
  · -- case x % 19 = 16 
    rw [h] at h1' 
    norm_num at h1' 
  · -- case x % 19 = 17 
    rw [h] at h1' 
    norm_num at h1' 
  · -- case x % 19 = 18 
    rw [h] at h1' 
    norm_num at h1'