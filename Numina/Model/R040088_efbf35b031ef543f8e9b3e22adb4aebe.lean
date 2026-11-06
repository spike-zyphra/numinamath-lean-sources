import Mathlib

theorem algebra_273960 {P : Polynomial ℤ} (hP : 6 ∣ P.eval 2 ∧ 6 ∣ P.eval 3) :
    6 ∣ P.eval 5 := by
  have h1 : 6 ∣ P.eval 2 := hP.1
  have h2 : 6 ∣ P.eval 3 := hP.2
  have h3 : (5 - 2 : ℤ) ∣ (P.eval 5 - P.eval 2) := by
    apply P.sub_dvd_eval_sub
  have h4 : 3 ∣ (P.eval 5 - P.eval 2) := by
    norm_num at h3 ⊢
    omega
  have h5 : (P.eval 5 - P.eval 2) % 3 = 0 := by
    omega
  have h6 : P.eval 2 % 3 = 0 := by
    omega
  have h7 : P.eval 5 % 3 = 0 := by
    omega
  -- $P(5) \equiv 0 \pmod{2}$ because $5 \equiv 3 \pmod{2}$ and $P(3) \equiv 0 \pmod{2}$.
  have h8 : (5 - 3 : ℤ) ∣ (P.eval 5 - P.eval 3) := by
    apply P.sub_dvd_eval_sub
  have h9 : 2 ∣ (P.eval 5 - P.eval 3) := by
    norm_num at h8 ⊢
    omega
  have h10 : (P.eval 5 - P.eval 3) % 2 = 0 := by
    omega
  have h11 : P.eval 3 % 2 = 0 := by
    omega
  have h12 : P.eval 5 % 2 = 0 := by
    omega
  omega