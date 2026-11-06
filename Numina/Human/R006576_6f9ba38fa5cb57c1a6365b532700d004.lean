import Mathlib

open Real 

open Nat


lemma nat_le_iff_lt_add_one : x ≤ y ↔ x < y + 1 := by
  omega



lemma nat_div_le_iff_le_mul (h : 0 < k) : x / k ≤ y ↔ x ≤ y * k + k - 1 := by
  rw [nat_le_iff_lt_add_one, Nat.div_lt_iff_lt_mul h, Nat.add_one_mul]
  omega


lemma nat_div_eq_iff (h : 0 < k) : x / k = y ↔ y * k ≤ x ∧ x ≤ y * k + k - 1 := by
  rw [Nat.eq_iff_le_and_ge, and_comm, le_div_iff_mul_le h, nat_div_le_iff_le_mul h]


lemma exist_rat {x : ℝ} (h : ¬ Irrational x) : ∃ (r : ℚ), x = r:= by 
    refine Rat.exists.mpr ?_
    by_contra hc1
    simp at hc1
    obtain aux := (irrational_iff_ne_rational _).mpr hc1
    exact h aux

lemma sq_of_rational_int (a : ℕ) : 
  ¬ Irrational (√a) → ∃ (n : ℕ), n ^ 2 = a := by
  intro h
  obtain ⟨r, hr⟩ := exist_rat h
  let x := r.num
  let y := r.den
  have aux :r = x / y := by 
    exact Eq.symm (Rat.num_div_den r)
  have aeq : (√↑a) ^ 2 = a := by 
    refine sq_sqrt ?_
    linarith
  have aux2 : (a : ℝ) = (↑x / ↑y) ^ 2 := by
    rw [←aeq, hr, aux]
    norm_cast
  have aux3 : (a : ℚ) = (↑x / ↑y) ^ 2  := by 
    norm_cast at aux2
    norm_cast
  rw [div_pow] at aux3
  have yneq : (y : ℚ) ≠ 0 := by 
    have aux4 : r.den ≠ 0 := by
      exact r.den_nz
    norm_cast
  have aux5 : (a : ℚ) * y ^ 2 = x ^ 2 := by 
    rw [aux3]
    field_simp
  norm_cast at aux5
  have aux6 : ∃ (x1 : ℕ), x = x1 := by 
    use x.toNat
    have xge : x ≥ 0 := by 
      have rge0 : r ≥ 0 := by 
        have pos : (r : ℝ) ≥ 0 := by 
          rw [←hr]
          positivity
        norm_cast at pos
      exact Rat.num_nonneg.mpr rge0
    omega
  obtain ⟨x1, hx1⟩ := aux6
  rw [hx1] at aux5
  norm_cast at aux5
  use (x1 / y)
  rw [Nat.div_pow]
  rw [←aux5]
  refine (nat_div_eq_iff ?_).mpr ?_
  positivity
  constructor
  linarith
  have aux1 : y ^ 2  ≥ 1:= by 
    have : (y : ℕ) ≥ 1 := by
      norm_cast at yneq
      omega
    calc 
      _ ≥ 1 ^ 2 := by 
        exact pow_le_pow_of_le_left this 2
      _ = 1 := by norm_num
  have aux2 : a * y ^ 2 + y ^ 2 - 1 = a * y ^ 2 + (y ^ 2 - 1) := by 
    norm_cast at yneq 
    omega
  rw [aux2]
  linarith
  have sq_dvd : y ^ 2 ∣ x1 ^ 2 := by 
    use a
    rw [←aux5]
    ring
  apply (Nat.pow_dvd_pow_iff (by norm_num)).mp at sq_dvd
  exact sq_dvd




theorem my_favorite_theorem (p q : ℕ) (h₀ : p ≠ 0 ∨ q ≠ 0) (h₁ : ¬ (∃ m, m^2 = p) ∨ ¬ (∃ n, n^2 = q)) :
  Irrational (Real.sqrt p + Real.sqrt q) := by 
  by_contra hc
  simp at hc
  have h1 : ¬ Irrational ((√↑p + √↑q) ^ 2) := by 
    by_contra hc1
    obtain aux := Irrational.of_pow 2 hc1
    exact hc aux
  have eq1 : (√↑p + √↑q) ^ 2 = p + q + 2 * √(p*q) := by
    ring_nf
    have aux1 : √↑p ^ 2 = ↑p := by 
      exact Real.sq_sqrt (by linarith)
    have aux2 : √↑q ^ 2 = ↑q := by 
      exact Real.sq_sqrt (by linarith)
    rw [aux1, aux2, sqrt_mul]
    ring_nf
    linarith
  rw [eq1] at h1
  -- irrational_rat_add_iff
  have h2 : ¬ Irrational (2 * √(p * q)) := by 
    by_contra hc1
    obtain aux := (irrational_rat_add_iff (q := p + q)).mpr hc1
    norm_num at aux
    norm_num at h1
    exact h1 aux
  have h3 : ¬ Irrational (√(p * q)) := by 
    by_contra hc1
    have neq : (2 : ℚ) ≠ 0 := by 
      norm_num
    obtain aux := Irrational.mul_rat hc1 neq
    rw [mul_comm] at h2
    norm_num at h2
    norm_num at aux
    exact h2 aux  
  obtain ⟨m, hm⟩ := sq_of_rational_int (p * q) (by norm_num; norm_num at h3; exact h3)
  have meq : m = √(p * q) := by
    refine Eq.symm ((fun {x y} => sqrt_eq_cases.mpr) ?_)
    constructor
    constructor
    norm_cast
    rw [←hm]
    ring
    linarith
  have hexist : ∃ (r : ℚ), (√↑p + √↑q) = r:= by 
    refine Rat.exists.mpr ?_
    by_contra hc1
    simp at hc1
    obtain aux := (irrational_iff_ne_rational _).mpr hc1
    exact hc aux
  obtain ⟨r, hr⟩ := exist_rat hc
  have h4 : ¬ Irrational (√p) := by 
    have aux : √↑q = ↑r - √↑p := by 
      linarith
    have aux1 : √p * (r - √p) = m := by 
      rw [meq]
      norm_num
      left
      linarith
    have aux2 : r * √ p = m + p := by 
      rw [←aux1]
      ring_nf
      have aux3 : √↑p ^ 2 = ↑p := by
        refine sq_sqrt ?_
        linarith
      rw [aux3]
      ring
    by_contra hc1
    have rneq0 : r ≠ 0 := by 
      have pos : r > 0 := by 
        obtain hp | hq := h₀
        have pos1 : √↑p >0 := by 
          refine sqrt_pos_of_pos ?_
          norm_cast
          omega
        have rpos : (r : ℝ) > 0 := by 
          rw [←hr]
          positivity
        norm_cast at rpos
        have rpos : (r : ℝ) > 0 := by 
          rw [←hr]
          positivity
        norm_cast at rpos
      linarith
    obtain hc2 := Irrational.rat_mul hc1 rneq0
    have aux3 : ¬  Irrational (↑r * √↑p) := by 
      rw [aux2]
      simp
    exact aux3 hc2
  obtain ⟨n, hn⟩ := sq_of_rational_int p (by exact h4)
  have h5 : ∃ l, l ^ 2 = q := by 
    
    rw [←hn] at hm
    by_cases peq0 : p = 0
    · 
      simp [peq0] at hr
      have aux : ¬Irrational √↑q := by 
        rw [hr]
        simp
      obtain ⟨z, hz⟩ := sq_of_rational_int q (by norm_cast)
      use z
    · 
      use (m / n)
      rw [Nat.div_pow]
      rw [hm]
      have nneq0 : n ≠ 0:= by 
        by_contra hn1
        rw [hn1] at hn
        simp at hn
        exact peq0 (Eq.symm hn)
      refine (nat_div_eq_iff ?_).mpr ?_
      positivity
      constructor
      linarith
      have aux1 : n ^ 2 - 1 ≥ 0 := by 
        omega
      have aux2 : q * n ^ 2 + n ^ 2 - 1 = q * n ^ 2 +( n ^ 2 - 1) := by 
        omega
      rw [aux2]
      linarith
      
      have sq_dvd : n ^ 2 ∣ m ^ 2 := by 
        use q
      apply (Nat.pow_dvd_pow_iff (by norm_num)).mp at sq_dvd
      exact sq_dvd
  obtain hp | hq := h₁
  apply hp
  use n
  norm_cast at hn
  
