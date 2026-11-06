import Mathlib

theorem number_theory_249742 (x y : ℕ) (h₀ : x + y = 667) (h₁ : Nat.lcm x y / Nat.gcd x y = 120) :
    x = 232 ∧ y = 435 ∨ 
    x = 552 ∧ y = 115 
    ∨
    x = 115 ∧ y = 552 ∨
    x = 435 ∧ y = 232 
    := by
  have x_pos : 0 < x := by 
    by_contra!
    simp_all
  have y_pos : 0 < y := by 
    by_contra!
    simp_all

  have : ∃ x1 y1 g, x = x1 * g ∧ y = y1 * g ∧ Nat.lcm x y = x1 * y1 * g ∧ Nat.gcd x y = g := by
    use x / Nat.gcd x y, y / Nat.gcd x y, Nat.gcd x y
    simp [x_pos, y_pos]
    rw [Nat.div_mul_cancel (Nat.gcd_dvd_left x y), Nat.div_mul_cancel (Nat.gcd_dvd_right x y)]
    simp
    have : x.gcd y * x.lcm y = (x / x.gcd y * x.gcd y) * ((y / x.gcd y) * x.gcd y) := by
      simp [Nat.gcd_mul_lcm]
      rw [Nat.div_mul_cancel (Nat.gcd_dvd_left x y), Nat.div_mul_cancel (Nat.gcd_dvd_right x y)]
    have : x.gcd y * x.lcm y =  x.gcd y * (x / x.gcd y * (y / x.gcd y) * x.gcd y) := by
      rw [this]
      ring
    apply Nat.mul_left_cancel _ this
    exact Nat.gcd_pos_of_pos_left y x_pos

    
  obtain ⟨x1, y1, g, hx1, hy1, hlcm, hgcd⟩ := this
  rw [hgcd] at h₁
  rw [hlcm] at h₁
  clear hlcm hgcd
  replace h₁ : x1 * y1 = 120 := by 
    rw [Nat.mul_div_cancel] at h₁
    exact h₁
    by_contra! h
    simp_all
  rw [hx1, hy1] at h₀ ⊢
  clear hx1 hy1
  have h_antidiag : x1 * g + y1 * g  = (x1 + y1) * g := by ring
  rw [h₀, mul_comm] at h_antidiag
  clear h₀
  have divisorsAntidiagonal_667 : 
      Nat.divisorsAntidiagonal 667 = {(1, 667), (23, 29), (29, 23), (667, 1)} := by 
    rw [<-Nat.map_div_right_divisors]
    rw [show 667 = 23 * 29 by norm_num]
    rw [Nat.divisors_mul]
    rw [Nat.Prime.divisors (by decide), Nat.Prime.divisors (by decide)]
    decide
  
  replace h_antidiag : (g, (x1 + y1)) ∈ ({(1, 667), (23, 29), (29, 23), (667, 1)} : Finset _) := by
    rw [<-divisorsAntidiagonal_667]
    simp only [Nat.mem_divisorsAntidiagonal, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      and_true]
    rw [h_antidiag]
  clear divisorsAntidiagonal_667
  simp only [Finset.mem_insert, Prod.mk.injEq, Finset.mem_singleton] at h_antidiag
  have divisorsAntidiagonal_120 : Nat.divisorsAntidiagonal 120 = {(1, 120), (2, 60), (3, 40), (4, 30), (5, 24), (6, 20), (8, 15), (10, 12), (12, 10), (15, 8), (20, 6), (24, 5), (30, 4), (40, 3), (60, 2), (120, 1)} := by
    rw [<-Nat.map_div_right_divisors]
    rw [show 120 = 2 * 2 * 2 * 3 * 5 by norm_num]
    simp_rw [Nat.divisors_mul]
    rw [Nat.Prime.divisors (by decide), Nat.Prime.divisors (by decide), Nat.Prime.divisors (by decide)]
    decide
  have h_antidiag' : (x1, y1) ∈ ({(1, 120), (2, 60), (3, 40), (4, 30), (5, 24), (6, 20), (8, 15), (10, 12), (12, 10), (15, 8), (20, 6), (24, 5), (30, 4), (40, 3), (60, 2), (120, 1)} : Finset _) := by
    rw [<-divisorsAntidiagonal_120]
    simp only [Nat.mem_divisorsAntidiagonal, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      and_true]
    rw [h₁]
  simp only [Finset.mem_insert, Prod.mk.injEq, Finset.mem_singleton] at h_antidiag'
  clear divisorsAntidiagonal_120 h₁
  rcases h_antidiag with ⟨hg, hxy⟩ | ⟨hg, hxy⟩ | ⟨hg, hxy⟩ | ⟨hg, hxy⟩ <;> subst g <;> 
  rcases h_antidiag' with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> subst_vars <;> simp_all
  
  
  
  
  
  