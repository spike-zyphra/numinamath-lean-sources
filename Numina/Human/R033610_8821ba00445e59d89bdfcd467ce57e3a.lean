import Mathlib

/- Let $a_{0}, a_{1}, a_{2}, \ldots$ be a sequence of positive real numbers satisfying $i \cdot a_{i}^{2} \geqslant(i+1) \cdot a_{i-1} a_{i+1}$ for $i=1,2, \ldots$ Furthermore, let $x$ and $y$ be positive reals, and let $b_{i}=x a_{i}+y a_{i-1}$ for $i=1,2, \ldots$ Prove that the inequality $i \cdot b_{i}^{2}>(i+1) \cdot b_{i-1} b_{i+1}$ holds for all integers $i \geqslant 2$. -/
theorem inequalities_240247 (a : ℕ → ℝ) (ha : ∀ i, 0 < a i) (h : ∀ i ≥ 1, i * (a i)^2 ≥ (i + 1) * a (i - 1) * a (i + 1)) : ∀ x y : ℝ, 0 < x → 0 < y → (∀ i ≥ 2, i * (x * a i + y * a (i - 1))^2 > (i + 1) * (x * a (i - 1) + y * a (i - 2)) * (x * a (i + 1) + y * a i)) := by
  intro x; intro y; intro xpos; intro ypos;
  intro i; intro ige2;

  -- some basic inequalities
  have _ : 0 < a i := ha i
  have _ : 0 < a (i-1) := ha (i-1)
  have _ : 0 < a (i-2) := ha (i-2)
  have _ : 0 < a (i+1) := ha (i+1)


  -- apply the assumtion for i and i-1.
  have iequ: i * (a i)^2 ≥ (i+1) * a (i-1) * a (i+1) := by apply h i; linarith
  have im1equ : (i-1) * (a (i-1))^2 ≥ i * (a (i-2)) * (a (i)):= by
    have tmp1: ↑(i - 1) * (a (i - 1)) ^ 2 ≥ (↑(i - 1) + 1) * a (i - 1 - 1) * a (i - 1 + 1):= by apply h (i-1); omega;
    have tmp2: (↑(i - 1) + 1) * a (i - 1 - 1) * a (i - 1 + 1) = i * (a (i-2)) * (a (i)) := by
      norm_cast
      have tmp3: (i -1 -1) = (i-2) := by omega
      have tmp4: (i-1+1) = i := by omega
      rw [tmp3]; rw [tmp4];
    rw [← tmp2];
    have _: ↑(i - 1) * a (i - 1) ^ 2 = (↑i - 1) * a (i - 1)^2 := by simp_all; left; apply Nat.cast_pred; linarith
    linarith
  have iim1mul : (i * (a i)^2) * ((i-1) * (a (i-1))^2) ≥ ((i+1) * a (i-1) * a (i+1)) * (i * (a (i-2)) * (a (i))) := by
    apply mul_le_mul_of_nonneg iequ im1equ; norm_cast; apply mul_nonneg; apply mul_nonneg; linarith; linarith; linarith; apply mul_nonneg; simp; linarith; nlinarith


  -- i x^2 a_i^2 ≥ (i+1) x^2 a_{i-1} a_{i+1}
  have ix2ai2 : i* x^2 * (a i)^2 ≥ (i+1) * x^2 * a (i-1) * a (i+1) := by
    have x2nonneg : 0 ≤  x^2 := by nlinarith
    have tmp2: i * (a i)^2 *x^2 ≥ (i+1) * a (i-1) *a (i+1) * x^2 := by apply mul_le_mul_of_nonneg_right iequ x2nonneg
    nlinarith

  -- i y^2 a_{i-1}^2 > (i+1) y^2 a_i a_{i-2}
  have iy2aim12 : i * y^2 * (a (i-1))^2 > (i+1) * y^2 * (a (i-2)) * (a (i)) := by
    have y2nonneg : 0<y^2 := by nlinarith
    -- \frac{a_{i-1}^{2}}{a_{i} a_{i-2}} \geqslant \frac{i}{i-1}=1+\frac{1}{i-1}&gt;1+\frac{1}{i}=\frac{i+1}{i}
    have tmp1: i * (a (i-1))^2 > (i+1) * a (i-2) * a (i) := by
      have tmp2: (a (i-1))^2 > a (i-2) * a (i) := by
        have tt: (a (i-1))^2 ≥ ↑(i)/↑(i -1) * a (i-2) * a (i) := by field_simp; field_simp at im1equ; rw [div_le_iff₀']; assumption; simp; linarith
        have _: (i:ℝ)/↑(i -1) > 1 := by
          have _: ↑(i -1) < (i:ℝ) := by norm_cast; omega
          have _: ↑(i -1) / ↑(i -1) < (i :ℝ ) / ↑(i -1) :=by apply div_lt_div₀; assumption; norm_cast; norm_cast; linarith; norm_cast; omega
          calc
            (i :ℝ ) / ↑(i -1) > ↑(i -1) / ↑(i -1) := by linarith
            _ = 1 := by apply div_self; norm_cast; by_contra; omega

        have ip1i: ↑(i)/↑(i -1) * a (i-2) * a (i) > 1 * a (i-2) * a (i) := by gcongr
        linarith
      calc
        i * (a (i-1))^2 = (i-1+1) * (a (i-1))^2:= by ring
        _ = (i-1) * (a (i-1))^2 + (a (i-1))^2:= by ring
        _ > (i-1) * (a (i-1))^2 + a (i-2) * a (i) := by gcongr
        _ ≥ i * (a (i-2)) * (a (i)) + a (i-2) * a (i) := by gcongr
        _ = (i+1) * a (i-2) * a i := by ring
    have _: i * (a (i-1))^2 * y^2 > (i+1) * a i * a (i-2)* y^2 := by nlinarith
    nlinarith

  -- i 2xy a_i a_{i-1} ≥ (i+1) xy (a_{i-2}a_{i+1} + a_{i-1}a_i)
  have i2xyaiaim1 : i * 2 * x * y * a i * a (i-1) ≥ (i+1) * x * y * (a (i-2)* a (i+1) + a (i-1) * a i) := by
    have _: (i-1) * a i * a (i-1) ≥ (i+1) * a (i-2) * a (i+1) := by
      repeat rw [pow_two] at iim1mul;
      field_simp at iim1mul; field_simp; nlinarith
    have _: i * 2 * a i * a (i-1) ≥ (i+1) * (a (i-2) * a (i+1) + a (i-1) * a i) := by nlinarith
    calc
      i * 2 * x * y * a i * a (i-1) = i * 2 * a i * a (i-1) * x * y := by ring
      _ ≥ (i+1) * (a (i-2) * a (i+1) + a (i-1) * a i) * x * y := by gcongr
      _ = (i+1) * x * y * (a (i-2)* a (i+1) + a (i-1) * a i) := by ring


  -- Adding all three inequalities together, we get the claim
  simp_all; linarith;
