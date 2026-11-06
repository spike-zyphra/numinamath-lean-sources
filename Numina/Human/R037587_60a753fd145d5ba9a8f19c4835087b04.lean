import Mathlib

/-Below is the graph of $y = a \sin (bx + c)$ for some positive constants $a,$ $b,$ and $c.$
Find $a.$

[asy]import TrigMacros;

size(300);

real f(real x)
{
	return 2*sin(4*x + pi/2);
}

draw(graph(f,-pi,pi,n=700,join=operator ..),red);
trig_axes(-pi,pi,-3,3,pi/2,1);
layer();
rm_trig_labels(-2,2, 2);

label("$1$", (0,1), E);
label("$2$", (0,2), E);
label("$-1$", (0,-1), E);
label("$-2$", (0,-2), E);
[/asy]-/
theorem calculus_22580 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : ∀ x, a * Real.sin (b * x + c) = 2 * Real.sin (4 * x + Real.pi / 2)) :
    a = 2 := by
  -- Take $x = 0$ and we have $a * \sin c = 2 \sin (\pi/2) = 2$.
  have h0 := h 0
  have h4 : Real.sin c = 2 / a := by
    field_simp [ha]
    rw [mul_comm]
    simpa using h0
  -- Then by $\sin c \le 1$ we have $2 / a \le 1$.
  have h5 : Real.sin c ≤ 1 := Real.sin_le_one c
  have h7 : 2 / a ≤ 1 := by linarith [h4]
  -- First we show that $a ≤ 2$
  have h8 : a ≤ 2 := by
    -- Take some x such that $a \sin (bx + c) = a$.
    have h10 : ∃ x : ℝ, Real.sin (b * x + c) = 1 := by
      use (Real.pi / 2 - c) / b
      have h11 : b * ((Real.pi / 2 - c) / b) + c = Real.pi / 2 := by
        field_simp [hb]
        ring
      rw [h11]
      exact Real.sin_pi_div_two
    rcases h10 with ⟨x, hx⟩
    -- Then we have $a \sin (bx + c) = a = 2 \sin (4x + \pi/2 ) $.
    have h9 := h x
    rw [hx] at h9
    -- Hence $\sin (4x + \pi/2 ) = a / 2$
    have h12 : Real.sin (4 * x + Real.pi / 2) = a / 2 := by
      nlinarith
    -- and by $\sin (4x + \pi/2 ) \le 1$ we have $a / 2 \le 1$.
    have h13 : Real.sin (4 * x + Real.pi / 2) ≤ 1 := Real.sin_le_one (4 * x + Real.pi / 2)
    rw [h12] at h13 
    rw [div_le_iff₀' (by norm_num), mul_one] at h13
    exact h13
  -- Now we show that $a ≥ 2$.
  have h9 : a ≥ 2 := by
    rw [div_le_iff₀ ha] at h7
    -- Since $2 / a \le 1 $ and $a > 0$ we have $a \ge 2$.
    linarith [h7]
  -- Finally we have $a = 2$.
  exact le_antisymm h8 h9
