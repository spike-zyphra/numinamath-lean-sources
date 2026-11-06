import Mathlib

theorem algebra_214716 {F : Polynomial ℤ} (hF1 : 5 ∣ F.eval 2) (hF2 : 2 ∣ F.eval 5) :
    10 ∣ F.eval 7 := by
  have h1 : (7 - 2 : ℤ) ∣ (F.eval 7 - F.eval 2) := by
    apply F.sub_dvd_eval_sub
  have h2 : 5 ∣ (F.eval 7 - F.eval 2) := by
    norm_num at h1 ⊢
    all_goals try exact h1
  -- From h2 we have $5$ divides $F(7) - F(2)$ and from hF1 we have $5$ divides $F(2)$.
  -- Therefore $5$ divides $F(7)$
  have h3 : 5 ∣ F.eval 7 := by
    have h4 : 5 ∣ (F.eval 7 - F.eval 2) := h2
    have h5 : 5 ∣ F.eval 2 := hF1
    have h6 : 5 ∣ (F.eval 7 - F.eval 2 + F.eval 2) := by
      apply Dvd.dvd.add
      exact h4
      exact h5
    have h7 : (F.eval 7 - F.eval 2 + F.eval 2) = F.eval 7 := by
      linarith
    rw [h7] at h6
    exact h6
  -- Now apply the property with a = 7 and b = 5
  have h4 : (7 - 5 : ℤ) ∣ (F.eval 7 - F.eval 5) := by
    apply F.sub_dvd_eval_sub
  have h5 : 2 ∣ (F.eval 7 - F.eval 5) := by
    norm_num at h4 ⊢
    all_goals try exact h4
  -- From h5 we have $2$ divides $F(7) - F(5)$ and from hF2 we have $2$ divides $F(5)$.
  -- Therefore $2$ divides $F(7)$
  have h6 : 2 ∣ F.eval 7 := by
    have h7 : 2 ∣ (F.eval 7 - F.eval 5) := h5
    have h8 : 2 ∣ F.eval 5 := hF2
    have h9 : 2 ∣ (F.eval 7 - F.eval 5 + F.eval 5) := by
      apply Dvd.dvd.add
      exact h7
      exact h8
    have h10 : (F.eval 7 - F.eval 5 + F.eval 5) = F.eval 7 := by
      linarith
    rw [h10] at h9
    exact h9
  -- Now we have $5$ divides $F(7)$ and $2$ divides $F(7)$, so $10$ divides $F(7)$
  have h7 : 10 ∣ F.eval 7 := by
    omega
  exact h7