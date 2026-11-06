import Mathlib
open Nat Real Finset Set
set_option linter.unusedVariables false

/-2000 distinct positive integers are written down, and it so happens that the product of any 3 different numbers from this list is a square. Prove that each one of them is a square.-/
theorem number_theory_600456
    (S : Finset ℕ)
    (hS_card : S.card = 2000)
    (hS_pos : ∀ x ∈ S, x > 0)
    (hS_prod_square : ∀ a ∈ S, ∀ b ∈ S,∀ c ∈ S, a ≠ b → a ≠ c → b ≠ c → ∃ k : ℕ, a * b * c = k * k) :
    ∀ x ∈ S, ∃ m : ℕ, x = m * m := by
  -- Take any $x$ in $S$ and aim to prove it is a square.
  intro x h_x
  have h_exists_bcd : ∃ b c d : ℕ, b ∈ S ∧ c ∈ S ∧ d ∈ S ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧ x ≠ b ∧ x ≠ c ∧ x ≠ d := by
    -- Since $S$ has $2000$ elements, we can choose $3$ distinct elements different from $x$.
    let T := S.erase x
    have h_T_card : T.card = 1999 := by
      rw [Finset.card_erase_of_mem h_x]
      simp [hS_card]
    have h_T_nonempty : T.Nonempty := by
      apply Finset.card_ne_zero.mp
      nlinarith [h_T_card]
    obtain ⟨b, h_b⟩ := h_T_nonempty
    let U := T.erase b
    have h_U_card : U.card = 1998 := by
      rw [Finset.card_erase_of_mem h_b, h_T_card]
    have h_U_nonempty : U.Nonempty := by
      apply Finset.card_ne_zero.mp
      nlinarith [h_U_card]
    obtain ⟨c, h_c⟩ := h_U_nonempty
    let V := U.erase c
    have h_V_card : V.card = 1997 := by
      rw [Finset.card_erase_of_mem h_c, h_U_card]
    have h_V_nonempty : V.Nonempty := by
      apply Finset.card_ne_zero.mp
      nlinarith [h_V_card]
    obtain ⟨d, h_d⟩ := h_V_nonempty
    -- Extract conditions from $h_b, h_c, h_d$.
    have h_b_split : b ≠ x ∧ b ∈ S := by rwa [Finset.mem_erase] at h_b
    have h_c_split : c ≠ x ∧ c ≠ b ∧ c ∈ S := by
      rw [Finset.mem_erase, Finset.mem_erase] at h_c
      exact ⟨h_c.2.1,h_c.1,h_c.2.2⟩
    have h_d_split : d ≠ x ∧ d ≠ b ∧ d ≠ c ∧ d ∈ S := by
      rw [Finset.mem_erase, Finset.mem_erase, Finset.mem_erase] at h_d
      exact ⟨h_d.2.2.1,h_d.2.1,⟨h_d.1, h_d.2.2.2⟩⟩
    use b, c, d
    exact ⟨h_b_split.2, h_c_split.2.2, h_d_split.2.2.2, h_c_split.2.1.symm, h_d_split.2.1.symm, h_d_split.2.2.1.symm,
           h_b_split.1.symm, h_c_split.1.symm, h_d_split.1.symm⟩
  -- For $b, c, d$ distinct and different from $x$, we have $a*b*c = p^2$, $a*b*d = q^2$, $a*c*d = r^2$.
  obtain ⟨b, c, d, h_b, h_c, h_d, h_bc, h_bd, h_cd, h_xb, h_xc, h_xd⟩ := h_exists_bcd
  have h_squares : ∃ p q r : ℕ, x * b * c = p * p ∧ x * b * d = q * q ∧ x * c * d = r * r := by
    have h_abc_square : ∃ p : ℕ, x * b * c = p * p := hS_prod_square x h_x b h_b c h_c h_xb h_xc h_bc
    have h_abd_square : ∃ q : ℕ, x * b * d = q * q := hS_prod_square x h_x b h_b d h_d h_xb h_xd h_bd
    have h_acd_square : ∃ r : ℕ, x * c * d = r * r := hS_prod_square x h_x c h_c d h_d h_xc h_xd h_cd
    obtain ⟨p, h_p⟩ := h_abc_square
    obtain ⟨q, h_q⟩ := h_abd_square
    obtain ⟨r, h_r⟩ := h_acd_square
    use p, q, r
  -- Multiply the equations: $x^3 * b^2 * c^2 * d^2 = p^2 * q^2 * r^2$.
  have h_product_eq : ∃ k : ℕ, x^3 * b^2 * c^2 * d^2 = k * k := by
    obtain ⟨p, q, r, h_abc, h_abd, h_acd⟩ := h_squares
    use p * q * r
    have h_left : x^3 * b^2 * c^2 * d^2 = (x * b * c) * (x * b * d) * (x * c * d) := by
      ring
    rw [h_abc, h_abd, h_acd] at h_left
    have : p * p * (q * q) * (r * r) = p * q * r * (p * q * r) := by ring
    rw [this] at h_left
    exact h_left
  -- Rearrange to get $x = (n * n) = m * m$.
  have h_x_square_eq : ∃ m n : ℕ, n ≠ 0 ∧ x * (n * n) = m * m := by
    obtain ⟨p, q, r, h_abc, h_abd, h_acd⟩ := h_squares
    obtain ⟨k, h_k_square⟩ := h_product_eq
    have h_n_pos : x * b * c * d > 0 := by
      simp [hS_pos x h_x, hS_pos b h_b, hS_pos c h_c, hS_pos d h_d]
    have h_n_nonzero : x * b * c * d ≠  0 := by omega
    have h_x_expr : x * (x * b * c * d)^2 = (p * q * r)^2 := by
      have h_x_cube : x^3 * b^2 * c^2 * d^2 = (p * q * r)^2 := by
        have h_left : x^3 * b^2 * c^2 * d^2 = (x * b * c) * (x * b * d) * (x * c * d) := by ring
        rw [h_abc, h_abd, h_acd] at h_left
        have : p * p * (q * q) * (r * r) = (p * q * r) ^ 2 := by ring
        rw [← this]
        exact h_left
      have h_left : x * (x * b * c * d)^2 = x^3 * b^2 * c^2 * d^2 := by ring
      rw [h_left, h_x_cube]
    use p * q * r, x * b * c * d
    constructor
    · exact h_n_nonzero
    · rw [← pow_two, ← pow_two]
      exact h_x_expr
  -- Since $x$ is an integer and a rational square, it is an integer square.
  have h_x_square : ∃ m : ℕ, x = m * m := by
    obtain ⟨m, n, h_n_nonzero, h_x_int⟩ := h_x_square_eq
    have h_n_nonzero : n ≠  0 := by omega
    have h_x_int : x * n * n = m * m := by rw [← mul_assoc] at h_x_int;exact h_x_int
    have : n * n ∣ m * m := by
      use x
      rw [mul_comm (n * n), ← mul_assoc]
      exact h_x_int.symm
    have : n ^2 ∣ m ^2 := by rw [← pow_two ,← pow_two] at this;exact this
    have h_n_dvd_m : n ∣ m := by
      apply (Nat.pow_dvd_pow_iff (by norm_num:2 ≠ 0)).mp
      exact this
    obtain ⟨k, h_m_k⟩ := h_n_dvd_m
    have h_x_k2 : x = k * k := by
      rw [h_m_k] at h_x_int
      have h_n_pos : n > 0 := Nat.pos_of_ne_zero h_n_nonzero
      nlinarith
    use k
  exact h_x_square
