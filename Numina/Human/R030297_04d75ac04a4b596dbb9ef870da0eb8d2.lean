import Mathlib

theorem algebra_215591 (x y : ℤ) (hx : x > 0) (hy : y > 0): (x + y) + (x - y) + x * y + (x:ℝ) / y = 2009 ↔ x = 246 ∧ y = 6 := by 

  constructor
  
  intro h

  --From left to right.
  simp at h
  have : ∃ k : ℤ, k = (x:ℝ) / y := by 
    use 2009 - 2*x - x*y; 
    field_simp at h ⊢
    ring_nf at h ⊢
    nlinarith
  obtain ⟨k,hk⟩ := this
  have : 0 < k := by 
    rify; 
    have t1: 0 < (x:ℝ) := by positivity
    have t2: 0 < (y:ℝ) := by positivity
    rw [hk]
    exact div_pos t1 t2

  --We rewrite the assumption to get (y+1)^2 ∣ 41 * 7^2.
  --Then, some analysis gives that y+1 can only be 7, so x = 246.
  have kyeq: k * (y+1)^2 = 2009 := by 
    rify
    rw [hk]
    rw [← h]
    field_simp
    ring_nf
  have myd: (y+1)^2 ∣ 2009 := by use k; linarith

  let l := (y+1).toNat
  have : l = y+1 := by omega
  have mydd: l^2 ∣ 2009 := by zify; rw [this]; exact myd
  have : 1 < l := by linarith

  have : 2009 = 41 * 7^2 := by norm_num
  rw [this] at mydd

  by_cases cop: Nat.Coprime (l^2) 41
  have : l^2 ∣ 7^2 := by exact Nat.Coprime.dvd_of_dvd_mul_left cop mydd
  rw [Nat.dvd_prime_pow] at this
  obtain ⟨i,⟨hi1,hi2⟩ ⟩ := this
  
  by_cases ie0 : i = 0
  rw [ie0] at hi2
  field_simp at hi2
  have : l = 1 := by exact Nat.eq_one_of_mul_eq_one_left hi2
  linarith
  
  by_cases ie1 : i = 1
  rw [ie1] at hi2
  field_simp at hi2
  exfalso
  have : l ∣ 7 := by use l; linarith
  have : l = 1 ∨ l = 7 := by 
    have p7: Nat.Prime 7 := by norm_num
    exact (Nat.dvd_prime p7).mp this
  rcases this with l1 | l7
  linarith
  rw [l7] at hi2; norm_num at hi2

  have ie2 : i = 2 := by omega
  rw [ie2] at hi2; field_simp at hi2
  have ye6: y = 6 := by linarith
  rw [ye6] at kyeq; 
  norm_num at kyeq
  have : k = 41 := by linarith
  rw [this,ye6] at hk
  have : x = 246 := by field_simp at hk; norm_num at hk; norm_cast at hk; linarith
  tauto
  norm_num

  have : Nat.Prime 41 := by norm_num
  have mycop : ¬(41).Coprime (l^2) := by 
    by_contra tmp
    have : (l^2).Coprime 41 := by exact Nat.coprime_comm.mp tmp
    contradiction
    
  have tmp: 41 ∣ l^2 := by 
    rw [←Nat.Prime.dvd_iff_not_coprime] at mycop
    exact mycop
    exact this
  have : 41 ∣ l := by exact Nat.Prime.dvd_of_dvd_pow this tmp
  have : 41^2 ∣ l^2 := by exact pow_dvd_pow_of_dvd this 2
  have : 41^2 ∣ 41 * 7^2 := by exact Nat.dvd_trans this mydd
  norm_num at this


  --From right to left, a simple calculation.
  intro ⟨xe,ye⟩
  simp [xe,ye]
  norm_num
