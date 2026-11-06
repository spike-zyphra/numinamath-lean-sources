import Mathlib

/- For how many pairs of primes $(p, q)$, is $p^2 + 2pq^2 + 1$ also a prime? -/
theorem number_theory_61972 :
  {(p, q) : ℕ × ℕ | p.Prime ∧ q.Prime ∧ (p ^ 2 + 2 * p * q ^ 2 + 1).Prime}.ncard = 1 := by

  --We prove that such pair can only be (2,3).
  have lem: {(p, q) : ℕ × ℕ | p.Prime ∧ q.Prime ∧ (p ^ 2 + 2 * p * q ^ 2 + 1).Prime} = {(2,3)} := by 
    ext ⟨x,y⟩
    simp

    constructor
    intro ⟨hx,hy,h⟩
    
    have xge2 : 2 ≤ x := by exact Nat.Prime.two_le hx
    have yge2 : 2 ≤ y := by exact Nat.Prime.two_le hy
    have : 2 < (x^2 + 2*x*y^2 + 1) := by nlinarith

    --By parity, we first show that p can only be even, so it is 2.
    have : Odd (x^2 + 2*x*y^2 + 1) := by 
      have : ¬ (x^2 + 2*x*y^2 + 1) = 2 := by linarith
      exact Nat.Prime.odd_of_ne_two h this
    
    have evenx: Even x := by 
      by_contra neven
      have oddx : Odd x := by exact Nat.not_even_iff_odd.mp neven
      have t1: Odd (x^2) := by exact Odd.pow oddx
      have t2: Even (2*x*y^2) := by use x*y^2; ring
      have : Odd (x^2+2*x*y^2) := by exact Even.odd_add t2 t1
      have : Even (x^2+2*x*y^2+1) := by exact Odd.add_one this
      have : x^2+2*x*y^2 + 1 =2 := by exact (Nat.Prime.even_iff h).mp this
      linarith
    have xe : x = 2 := by exact (Nat.Prime.even_iff hx).mp evenx

    rw [xe] at h
    ring_nf at h

    --Then, by considering mod 3, we have that y must equal 0 mod 3, so y = 3.
    have ye : y = 3 := by 
      have : y % 3 = 0 := by 
        by_contra ym3neq0
        have : y^2 % 3 = 1 := by
          by_cases ym1 : y % 3 = 1
          have : y^2 % 3 = 1 := by rw [Nat.pow_mod]; rw [ym1]
          exact this
          have ym2 : y % 3 = 2 := by omega
          have : y^2 % 3 = 1 := by rw [Nat.pow_mod]; rw [ym2]
          exact this
        have : (y^2 * 4)%3 = 1 := by omega
        have : (5 + (y^2*4)) % 3 = 0 := by omega
        have : 3 ∣ (5+(y^2*4)) := by exact Nat.dvd_of_mod_eq_zero this
        have : 5+(y^2 *4) = 3 := by 
          rw [Nat.dvd_prime] at this;
          simp at this
          symm
          exact this
          exact h
        omega
      have : 3 ∣ y := by exact Nat.dvd_of_mod_eq_zero this
      have : y = 3 := by rw [Nat.dvd_prime] at this; simp at this; symm; assumption; exact hy
      exact this

    tauto
      
    --Simple verification to show that (2,3) is valid.
    intro ⟨xe,ye⟩
    simp [xe,ye]
    norm_num
  
  
  simp [lem]