import Mathlib

/-
## 7. Natural Fraction

What is the sum of all natural numbers $n$ for which the fraction

$$
\frac{6 n+900}{2 n-3}
$$

is a natural number?

Result: $\quad 672$
-/

theorem number_theory_252431 (S:Finset ℕ) (h: ∀n, n ∈ S ↔ 2*n-3 ≠ 0 ∧ (∃m:ℕ, (m = ((6*(n:ℚ)+900)/(2*n-3))))) : ∑ n ∈ S, n = 672 := by

  --We prove that S= {2,3,6,52,153,456}.
  have cla : S = {2,3,6,52,153,456} := by 
    ext n
    simp [h]

    constructor

    --If 2n-3 ∣ 6*n+900, then 2n-3 ∣ 909.
    intro h
    obtain ⟨nu, m, hm⟩ := h
    have nuneq: 2 * (n:ℚ) - 3 ≠ 0 := by 
      by_contra eq
      have : 2 * (n:ℚ) = 3 := by linarith only [eq]
      norm_cast at this
      omega
    field_simp [nuneq] at hm
    have nupos: 0 < 2 * (n:ℚ) - 3 := by nlinarith
    have nuzpos : 0 < 2*n-3 := by omega
    let nn :ℕ  := 2*n-3
    have d1: nn ∣ 6*n + 900 := by 
      use m
      simp [nn]
      qify
      rw [← hm]
      have : @Nat.cast ℚ AddMonoidWithOne.toNatCast (2 * n - 3)  = @HSub.hSub ℚ ℚ ℚ instHSub (2 * ↑n) 3 := by 
        norm_cast
        refine Eq.symm (Int.subNatNat_of_le ?_)
        omega
      rw [this]
      ring
    have d2: nn ∣ 3*nn := by use 3; ring
    have dd : nn ∣ 909 := by 
      have t1: nn ∣ 6*n+900 - 3*nn := by exact Nat.dvd_sub' d1 d2
      have : 6*n+900 - 3*nn = 909 := by simp [nn]; omega
      rw [this] at t1
      exact t1
    
    --Now we find what are divisors of 909.
    have di909 : Nat.divisors 909 = {1,3,9,101,303,909} := by native_decide
    have : nn ∈ Nat.divisors 909 := by rw [@Nat.mem_divisors]; simp [dd]
    rw [di909] at this
    simp at this
    --We enumerate the possible value of 2n-3.
    rcases this with hnn | hnn | hnn | hnn | hnn | hnn <;> simp [nn] at hnn <;> omega
      

    --The other direction is just simple verification.
    intro h
    rcases h with h | h | h | h | h | h
    
    field_simp [h]
    norm_num
    use 912
    norm_num

    field_simp [h]
    norm_num
    use 306
    norm_num

    field_simp [h]
    norm_num
    use 104
    norm_num

    field_simp [h]
    norm_num
    use 12
    norm_num

    field_simp [h]
    norm_num
    use 6
    norm_num

    field_simp [h]
    norm_num
    use 4
    norm_num



  simp [cla]