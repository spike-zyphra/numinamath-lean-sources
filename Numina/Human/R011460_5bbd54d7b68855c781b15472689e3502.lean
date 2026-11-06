import Mathlib

/- Prove that for any positive reals $ a,b,c,d $ with $ a+b+c+d = 4 $, we have $$ \sum\limits_{cyc}{\frac{3a^3}{a^2+ab+b^2}}+\sum\limits_{cyc}{\frac{2ab}{a+b}} \ge 8 $$ -/
theorem inequalities_26053 (x : Fin 4 → ℝ) (hx : ∀ i, 0 < x i)
    (h : x 0 + x 1 + x 2 + x 3 = 4 /- ∑ i, x i = 4 -/) :
    (∑ i, let a := x i; let b := x (i + 1); 3 * a ^ 3 / (a ^ 2 + a * b + b ^ 2)) +
    (∑ i, let a := x i; let b := x (i + 1); 2 * a * b / (a + b)) ≥ 8 := by
  -- we have $a^3-b^3=(a-b)(a^2+ab+b^2)$ , so it's easy to find that $\sum_{cyc}\frac{3a^3}{a^2+ab+b^2}=\sum_{cyc}\frac{3b^3}{a^2+ab+b^2}$ .\
  set sum_a_cubic_div := ∑ i, let a := x i; let b := x (i + 1); 3 * a ^ 3 / (a ^ 2 + a * b + b ^ 2)
  let sum_b_cubic_div := ∑ i, let a := x i; let b := x (i + 1); 3 * b ^ 3 / (a ^ 2 + a * b + b ^ 2)
  have sum_cubic_div_eq : sum_a_cubic_div = sum_b_cubic_div := by
    suffices sum_a_cubic_div - sum_b_cubic_div = 0 by
      linarith
    let f i := let a := x i; let b := x (i + 1); 3 * (a - b)
    have : sum_a_cubic_div - sum_b_cubic_div =
        ∑ i, f i /- (3 * a ^ 3 - 3 * b ^ 3) / (a ^ 2 + a * b + b ^ 2) -/ := by
      rw [←Finset.sum_sub_distrib]
      congr
      --simp
      ext i
      set a := x i
      set b := x (i + 1)
      simp
      have : 3 * a ^ 3 / (a ^ 2 + a * b + b ^ 2) - 3 * b ^ 3 / (a ^ 2 + a * b + b ^ 2) =
          (3 * a ^ 3 - 3 * b ^ 3) / (a ^ 2 + a * b + b ^ 2) := by
        ring
      rw [this]
      have : 3 * a ^ 3 - 3 * b ^ 3 = 3 * (a - b) * (a ^ 2 + a * b + b ^ 2) := by
        ring
      rw [this]
      have : a ^ 2 + a * b + b ^ 2 > 0 := by
        have := hx i
        have := hx (i + 1)
        nlinarith
      field_simp
    rw [this]
    have := Fin.sum_univ_four f
    rw [this]
    ring_nf
    have : (4 : Fin 4) = 0 :=
      rfl
    rw [this]
    ring
  -- now we proof : $ \sum\limits_{cyc}{\frac{3a^3}{a^2+ab+b^2}}+\sum_{cyc}\frac{3b^3}{a^2+ab+b^2}+\sum\limits_{cyc}{\frac{4ab}{a+b}} \ge 16 $
  suffices sum_a_cubic_div + sum_b_cubic_div +
      (∑ i, (let a := x i; let b := x (i + 1); 4 * a * b / (a + b))) ≥ 16 by
    rw [←sum_cubic_div_eq] at this
    rw [show sum_a_cubic_div + sum_a_cubic_div = 2 * sum_a_cubic_div by ring] at this
    have : (∑ i : Fin 4, let a := x i; let b := x (i + 1); 4 * a * b / (a + b)) =
        (2 * ∑ i : Fin 4, let a := x i; let b := x (i + 1); 2 * a * b / (a + b)) := by
      have : (∑ i : Fin 4, let a := x i; let b := x (i + 1); 4 * a * b / (a + b)) =
          (∑ i : Fin 4, let a := x i; let b := x (i + 1); 2 * (2 * a * b / (a + b))) := by
        congr
        ext i
        ring
      rw [this]
      exact
        Eq.symm
          (Finset.mul_sum Finset.univ
            (fun i ↦
              let a := x i;
              let b := x (i + 1);
              2 * a * b / (a + b))
            2)
    linarith
  -- actually we have $\frac{3a^3}{a^2+ab+b^2}+\frac{3b^3}{a^2+ab+b^2}\ge \frac{2a^2+2b^2}{a+b}$\
  -- so $L.H.S\ge \sum_{cyc}\frac{2a^2+2b^2}{a+b}+\sum\limits_{cyc}{\frac{4ab}{a+b}}=\sum_{cyc}(2a+2b)=16$ .\
  let f_helper (a b : ℝ) := (3 * a ^ 3 + 3 * b ^ 3) / (a ^ 2 + a * b + b ^ 2) + (4 * a * b) / (a + b)
  let f i := f_helper (x i) (x (i + 1))
  suffices ∑ i, f i ≥ 16 by
    unfold sum_a_cubic_div sum_b_cubic_div
    rw [←Finset.sum_add_distrib, ←Finset.sum_add_distrib]
    convert this using 2
    rename_i i i_in_univ
    ring
  have ge_a_b a b (a_pos : a > 0) (b_pos : b > 0) : f_helper a b ≥ 2 * (a + b) := by
    have : (3 * a ^ 3 + 3 * b ^ 3) / (a ^ 2 + a * b + b ^ 2) ≥ (2 * a ^ 2 + 2 * b ^ 2) / (a + b) := by
      have left_den_pos : a ^ 2 + a * b + b ^ 2 > 0 := by nlinarith
      have right_den_pos : a + b > 0 := by linarith
      have mul_ge : (3 * a ^ 3 + 3 * b ^ 3) * (a + b) ≥ (2 * a ^ 2 + 2 * b ^ 2) * (a ^ 2 + a * b + b ^ 2) := by
        ring_nf
        suffices a ^ 4 + a * b ^ 3 + a ^ 3 * b + b ^ 4 ≥ a ^ 2 * b ^ 2 * 4 by
          linarith
        have : (a ^ 2) ^ 2 + (b ^ 2) ^ 2 ≥ 2 * a ^ 2 * b ^ 2 := by
          exact two_mul_le_add_sq (a ^ 2) (b ^ 2)
        have := two_mul_le_add_sq a b
        have : (2 * a * b) * (a * b) ≤ (a ^ 2 + b ^ 2) * (a * b) := by
          have : a * b ≥ 0 := by nlinarith
          nlinarith
        linarith
      exact (div_le_div_iff₀ right_den_pos left_den_pos).mpr mul_ge --nlinarith
    unfold f_helper
    calc
      (3 * a ^ 3 + 3 * b ^ 3) / (a ^ 2 + a * b + b ^ 2) + 4 * a * b / (a + b) ≥ (2 * a ^ 2 + 2 * b ^ 2) / (a + b) + 4 * a * b / (a + b) := by gcongr
      --_ = (2 * a ^ 2 + 4 * a * b + 2 * b ^ 2) / (a + b) := by ring
      _ = 2 * (a + b) ^ 2 / (a + b) := by ring
      _ = 2 * (a + b) := by
        field_simp
        ring
  set g := fun i => let a := x i; let b := x (i + 1); 2 * (a + b)
  have sum_ge : Finset.univ.sum f ≥ Finset.univ.sum g := by
    have : f ≥ g := by
      exact fun i ↦ ge_a_b (x i) (x (i + 1)) (hx i) (hx (i + 1))
    exact Finset.sum_le_sum fun i i_in_univ ↦ this i
  have : Finset.univ.sum g = 16 := by
    --simp [g, Finset.sum]
    --ring_nf
    have : Finset.univ.sum g = g 0 + g 1 + g 2 + g 3 := by
      exact Fin.sum_univ_four g
    rw [this]
    simp [g]
    linarith
  rw [this] at sum_ge
  exact sum_ge
  -- so we are done. :D
