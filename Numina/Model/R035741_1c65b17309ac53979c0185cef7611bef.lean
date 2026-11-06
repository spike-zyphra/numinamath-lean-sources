import Mathlib

theorem algebra_126780 {P : Polynomial ℤ} (hP : ∃ x y z, x ≠ y ∧ y ≠ z ∧ z ≠ x ∧ |P.eval x| = 1 ∧ |P.eval y| = 1 ∧ |P.eval z| = 1) :
    ¬∃ x : ℤ, P.eval x = 0 := by
  rintro ⟨r, hr⟩
  rcases hP with ⟨x, y, z, hx1, hy1, hz1, hx2, hy2, hz2⟩
  have h1 : P.eval x = 1 ∨ P.eval x = -1 := by
    cases eq_or_eq_neg_of_abs_eq hx2 with
    | inl h => tauto
    | inr h => tauto
  have h2 : P.eval y = 1 ∨ P.eval y = -1 := by
    cases eq_or_eq_neg_of_abs_eq hy2 with
    | inl h => tauto
    | inr h => tauto
  have h3 : P.eval z = 1 ∨ P.eval z = -1 := by
    cases eq_or_eq_neg_of_abs_eq hz2 with
    | inl h => tauto
    | inr h => tauto
  have h4 : (r - x) ∣ (P.eval r - P.eval x) := by
    apply P.sub_dvd_eval_sub
  rw [hr] at h4
  have h5 : (r - y) ∣ (P.eval r - P.eval y) := by
    apply P.sub_dvd_eval_sub
  rw [hr] at h5
  have h6 : (r - z) ∣ (P.eval r - P.eval z) := by
    apply P.sub_dvd_eval_sub
  rw [hr] at h6
  have h7 : (r - x) ∣ (P.eval x) := by
    have hdiv : (r - x) ∣ (-P.eval x) := by
      simpa using h4
    exact Int.dvd_neg.mp hdiv 
  have h8 : (r - x) = 1 ∨ (r - x) = -1 := by
    have h31 : (r - x) ∣ 1 := by
      have h41 : (r - x) ∣ P.eval x := h7 
      have h9 : P.eval x = 1 ∨ P.eval x = -1 := h1
      rcases h9 with (h | h)
      · -- If P.eval x = 1
        have h10 : (r - x) ∣ 1 := by 
          rw [h] at h41 
          exact h41 
        assumption 
      · -- If P.eval x = -1 
        have h10 : (r - x) ∣ 1 := by 
          rw [h] at h41 
          have hdiv : (r - x) ∣ (-1 : ℤ) := by 
            simpa using h41 
          have h14 : (r - x) ∣ (1 : ℤ) := by 
            exact Int.dvd_neg.mp hdiv 
          assumption 
        assumption 
    have h11 : (r - x) = 1 ∨ (r - x) = -1 := by
      have h8 : (r - x) ∣ 1 := h31 
      have h11 : (r - x) ≤ 1 := by 
        exact Int.le_of_dvd (by norm_num) h8 
      have h12 : (r - x) ≥ -1 := by 
        have h13 : - (r - x) ∣ 1 := by 
          exact Int.neg_dvd.2 h8 
        have h14 : - (r - x) ≤ 1 := by 
          exact Int.le_of_dvd (by norm_num) h13 
        omega 
      interval_cases (r - x) <;> tauto 
    assumption 
  have h8y : (r - y) = 1 ∨ (r - y) = -1 := by
    have h31 : (r - y) ∣ 1 := by 
      have h41 : (r - y) ∣ P.eval y := by 
        have hdiv : (r - y) ∣ (-P.eval y) := by 
          simpa using h5 
        exact Int.dvd_neg.mp hdiv 
      have h9 : P.eval y = 1 ∨ P.eval y = -1 := h2
      rcases h9 with (h | h)
      · -- If P.eval y = 1 
        have h10 : (r - y) ∣ 1 := by 
          rw [h] at h41 
          exact h41 
        assumption 
      · -- If P.eval y = -1 
        have h10 : (r - y) ∣ 1 := by 
          rw [h] at h41 
          have hdiv : (r - y) ∣ (-1 : ℤ) := by 
            simpa using h41 
          have h14 : (r - y) ∣ (1 : ℤ) := by 
            exact Int.dvd_neg.mp hdiv 
          assumption 
        assumption 
    have h11 : (r - y) = 1 ∨ (r - y) = -1 := by 
      have h8 : (r - y) ∣ 1 := h31 
      have h11 : (r - y) ≤ 1 := by 
        exact Int.le_of_dvd (by norm_num) h8 
      have h12 : (r - y) ≥ -1 := by 
        have h13 : - (r - y) ∣ 1 := by 
          exact Int.neg_dvd.2 h8 
        have h14 : - (r - y) ≤ 1 := by 
          exact Int.le_of_dvd (by norm_num) h13 
        omega 
      interval_cases (r - y) <;> tauto 
    assumption 
  have h8z : (r - z) = 1 ∨ (r - z) = -1 := by 
    have h31 : (r - z) ∣ 1 := by 
      have h41 : (r - z) ∣ P.eval z := by 
        have hdiv : (r - z) ∣ (-P.eval z) := by 
          simpa using h6 
        exact Int.dvd_neg.mp hdiv 
      have h9 : P.eval z = 1 ∨ P.eval z = -1 := h3
      rcases h9 with (h | h)
      · -- If P.eval z = 1 
        have h10 : (r - z) ∣ 1 := by 
          rw [h] at h41 
          exact h41 
        assumption 
      · -- If P.eval z = -1 
        have h10 : (r - z) ∣ 1 := by 
          rw [h] at h41 
          have hdiv : (r - z) ∣ (-1 : ℤ) := by 
            simpa using h41 
          have h14 : (r - z) ∣ (1 : ℤ) := by 
            exact Int.dvd_neg.mp hdiv 
          assumption 
        assumption 
    have h11 : (r - z) = 1 ∨ (r - z) = -1 := by 
      have h8 : (r - z) ∣ 1 := h31 
      have h11 : (r - z) ≤ 1 := by 
        exact Int.le_of_dvd (by norm_num) h8 
      have h12 : (r - z) ≥ -1 := by 
        have h13 : - (r - z) ∣ 1 := by 
          exact Int.neg_dvd.2 h8 
        have h14 : - (r - z) ≤ 1 := by 
          exact Int.le_of_dvd (by norm_num) h13 
        omega 
      interval_cases (r - z) <;> tauto 
    assumption 
  omega