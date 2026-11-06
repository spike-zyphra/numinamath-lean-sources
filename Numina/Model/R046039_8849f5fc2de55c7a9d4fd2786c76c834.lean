import Mathlib

theorem algebra_191849 {P : Polynomial ℤ} (hP1 : P.eval 2 ≡ 0 [ZMOD 6]) (hP2 : P.eval 3 ≡ 0 [ZMOD 6]) :
    P.eval 5 ≡ 0 [ZMOD 6] := by 
  -- Show $P(5) \equiv P(3) \pmod{2}$ since $5 \equiv 3 \pmod{2}$
  have h1 : (5 : ℤ) % 2 = (3 : ℤ) % 2 := by 
    norm_num 
  -- Show $P(5) \equiv P(3) \pmod{2}$ using the property of polynomials
  have h2 : (P.eval 5 : ℤ) % 2 = (P.eval 3 : ℤ) % 2 := by 
    have h7 : (5 - 3 : ℤ) ∣ ((P.eval 5 : ℤ) - (P.eval 3 : ℤ)) := by 
      apply P.sub_dvd_eval_sub 
    have h8 : (5 - 3 : ℤ) = (2 : ℤ) := by 
      norm_num 
    rw [h8] at h7 
    have h9 : (2 : ℤ) ∣ ((P.eval 5 : ℤ) - (P.eval 3 : ℤ)) := h7 
    omega 
  -- Show $P(3) \equiv 0 \pmod{2}$ from $P(3) \equiv 0 \pmod{6}$
  have h3 : (P.eval 3 : ℤ) % 2 = 0 := by 
    have h4 : P.eval 3 % 6 = 0 := by 
      norm_num [Int.ModEq] at hP2 ⊢ 
      omega 
    omega 
  -- Conclude $P(5) \equiv 0 \pmod{2}$
  have h4 : (P.eval 5 : ℤ) % 2 = 0 := by 
    omega 
  -- Show $P(5) \equiv P(2) \pmod{3}$ since $5 \equiv 2 \pmod{3}$
  have h5 : (5 : ℤ) % 3 = (2 : ℤ) % 3 := by 
    norm_num 
  -- Show $P(5) \equiv P(2) \pmod{3}$ using the property of polynomials
  have h6 : (P.eval 5 : ℤ) % 3 = (P.eval 2 : ℤ) % 3 := by 
    have h9 : (5 - 2 : ℤ) ∣ ((P.eval 5 : ℤ) - (P.eval 2 : ℤ)) := by 
      apply P.sub_dvd_eval_sub 
    have h10 : (5 - 2 : ℤ) = (3 : ℤ) := by 
      norm_num 
    rw [h10] at h9 
    have h11 : (3 : ℤ) ∣ ((P.eval 5 : ℤ) - (P.eval 2 : ℤ)) := h9 
    omega 
  -- Show $P(2) \equiv 0 \pmod{3}$ from $P(2) \equiv 0 \pmod{6}$
  have h7 : (P.eval 2 : ℤ) % 3 = 0 := by 
    have h8 : P.eval 2 % 6 = 0 := by 
      norm_num [Int.ModEq] at hP1 ⊢ 
      omega 
    omega 
  -- Conclude $P(5) \equiv 0 \pmod{3}$
  have h8 : (P.eval 5 : ℤ) % 3 = 0 := by 
    omega 
  -- Prove $P(5) \equiv 0 \pmod{6}$ from $P(5) \equiv 0 \pmod{2}$ and $P(5) \equiv 0 \pmod{3}$
  norm_num [Int.ModEq] at hP1 hP2 ⊢ 
  omega