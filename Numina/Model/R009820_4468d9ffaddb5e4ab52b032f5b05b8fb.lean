import Mathlib

theorem number_theory_163284 (n : ℕ) :
    ¬ ∃ m : ℤ, m^2 = ⌊(2 * √(n + 1)) / (√(n + 1) - √n)⌋ := by
-- We will multiply and divide by the conjugate to remove the denominator:
  have conj : (2 * √(n + 1)) / (√(n + 1) - √n) = 2*n+2 + 2*√n*√(n + 1) := by
    calc (2 * √(n + 1)) / (√(n + 1) - √n)
      _ = (2 * √(n + 1)) / (√(n + 1) - √n) * ((√(n + 1) + √n) / (√(n + 1) + √n)) := by
          field_simp
      _ = (2 * √(n + 1)) * ((√(n + 1) + √n)) / ((√(n + 1) - √n) * (√(n + 1) + √n)) := 
          div_mul_div_comm (2 * √(n + 1)) (√(n + 1) - √n) (√(n + 1) + √n) (√(n + 1) + √n)
      _ = (2 * √(n + 1)) * ((√(n + 1) + √n)) / 1 := by 
          have : (√(n + 1) - √n) * (√(n + 1) + √n) = 1 := by
            have : (√(n + 1) - √n) * (√(n + 1) + √n) = √(n + 1)^2 - √n^2 := by linarith
            have : √(n + 1)^2 - √n^2 = n+1 - n := by field_simp
            linarith
          rw [this]
      _ = (2 * √(n + 1)) * ((√(n + 1) + √n)) := by simp
      _ = (2 * √(n + 1)) * √(n + 1) + (2 * √(n + 1)) * √n := by rw [mul_add]
      _ = 2 * (√(n + 1) * √(n + 1)) + (2 * √(n + 1)) * √n := by rw [mul_assoc]
      _ = 2 * (n + 1) + (2 * √(n + 1)) * √n :=  by rw [Real.mul_self_sqrt]; linarith
      _ = 2 * n + 2 + 2 * √n * √(n + 1) := by linarith
  have conj_floor : ⌊2*n+2 + 2*√n*√(n + 1)⌋ = 4*n+2 :=  by
    have : ⌊(2*n+2) + 2*√n*√(n + 1)⌋ = (2*n+2) + ⌊2*√n*√(n + 1)⌋ :=  by
      rw [← Int.floor_int_add]; norm_cast
    rw [this]
    have : ⌊2*√n*√(n + 1)⌋ = 2*n :=  by 
      have : 2*n ≤ 2*√n*√(n + 1) :=  by 
        have : n ≤ √n*√(n + 1) :=  by 
          have neq : n = √n*√n :=  by simp [Nat.cast_nonneg, Real.mul_self_sqrt]
          nth_rw 1 [neq]
          apply mul_le_mul
          . linarith
          . gcongr; linarith
          . exact Real.sqrt_nonneg n
          . exact Real.sqrt_nonneg n
        linarith
      have : 2*√n*√(n + 1) < 2*n+1 :=  by 
        have help : √(n*(n+1)) < √((n+1/2)^2) :=  by
          apply Real.sqrt_lt_sqrt
          . apply mul_nonneg <;> linarith
          . linarith
        calc 2*√n*√(n+1)
          _ = 2*√(n*(n+1)) :=  by rw [Real.sqrt_mul] <;> linarith
          _ < 2*√((n+1/2)^2) :=  by
              apply (mul_lt_mul_iff_of_pos_left _).mpr
              . exact  help
              . linarith
          _ = 2*(n+1/2 : ℝ) :=  by rw [Real.sqrt_sq]; linarith
          _ = (2*n+1 : ℝ) :=  by linarith
      apply  Int.floor_eq_iff.mpr
      constructor <;> 
      simp_all only [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
    linarith
  have : ⌊(2 * √(n + 1)) / (√(n + 1) - √n)⌋ = 4*n+2 :=  by rw [conj, conj_floor]
  intro h
  rcases h with ⟨m, hm⟩ 
  rw [this] at hm 
  have h1 : m^2 = 4 * n + 2 :=  by linarith 
  have h2 : m^2 % 8 = 0 ∨ m^2 % 8 = 1 ∨ m^2 % 8 = 4 := by
    have h : m % 8 = 0 ∨ m % 8 = 1 ∨ m % 8 = 2 ∨ m % 8 = 3 ∨ m % 8 = 4 ∨ m % 8 = 5 ∨ m % 8 = 6 ∨ m % 8 = 7 :=  by omega
    rcases h with (h | h | h | h | h | h | h | h) <;> norm_num [pow_two, Int.mul_emod, Int.add_emod, Int.sub_emod, h]
  have h3 : (4 * n + 2) % 8 = 2 ∨ (4 * n + 2) % 8 = 6 :=  by 
    omega
  have h4 : m^2 % 8 = (4 * n + 2) % 8 :=  by 
    omega
  omega