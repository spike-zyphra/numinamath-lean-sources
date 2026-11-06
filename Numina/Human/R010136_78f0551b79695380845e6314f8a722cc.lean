import Mathlib

/- Prouver que, pour tous réels $a, b, c>0$ et tout réel $t \geqslant 0$, on a

$$
\frac{a}{b+t c}+\frac{b}{c+t a}+\frac{c}{a+t b} \geqslant \frac{3}{1+t} .
$$ -/
theorem inequalities_604545 (a b c t : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (ht : 0 ≤ t) :
  3 / (1 + t) ≤ a / (b + t * c) + b / (c + t * a) + c / (a + t * b) := by
    -- AM-GM inequality for three variables.
    have am_gm {x y z : ℝ} (xpos : 0 < x) (ypos : 0 < y) (zpos : 0 < z) :
      z / x + x / y + y /z ≥ 3 := by
        suffices (z / x)^(1 / (3 : ℝ)) * (x / y)^(1 / (3 : ℝ)) * (y / z)^(1 / (3 : ℝ)) ≤ 1/3 * (z / x + x / y + y /z) by
          rw [←Real.mul_rpow, ←Real.mul_rpow] at this
          simp [show z / x * (x / y) * (y / z) = 1 by field_simp] at this
          nlinarith
          all_goals positivity
        simp only [mul_add]
        have h13: (0 : ℝ) ≤ 1 / 3 := by norm_num
        exact Real.geom_mean_le_arith_mean3_weighted h13 h13 h13 (by positivity) (by positivity) (by positivity) (by linarith)
    -- Let $x=b+t c, y=c+t a, z=a+t b$. 
    set x := b + t * c
    set y := c + t * a
    set z := a + t * b
    -- We verify that x y z are positive.
    have xpos : 0 < x := by positivity
    have ypos : 0 < y := by positivity
    have zpos : 0 < z := by positivity
    -- We verify that
    -- $$ \begin{aligned} \left(1+t^{3}\right) a & =z-t x+t^{2} y \ \left(1+t^{3}\right) b & =x-t y+t^{2} z \ \left(1+t^{3}\right) c & =y-t z+t^{2} x \end{aligned} $$
    have ha' : (1 + t^3) * a = z - t * x + t^2 * y := by
      simp [x, y, z]; try nlinarith
    have hb' : (1 + t^3) * b = x - t * y + t^2 * z := by
      simp [x, y, z]; try nlinarith
    have hc' : (1 + t^3) * c = y - t * z + t^2 * x := by
      simp [x, y, z]; try nlinarith
    suffices (1 + t^3) * (3 / (1 + t)) ≤ (1 + t^3) * (a / x + b / y + c / z) from (mul_le_mul_left (by positivity)).1 this
    simp only [mul_add, ←mul_div_assoc, ha', hb', hc']
    simp [add_div, sub_div]
    -- thus, according to the arithmetic-geometric mean inequality,
    -- $$ \begin{aligned} \left(1+t^{3}\right)\left(\frac{a}{b+t c}+\frac{b}{c+t a}+\frac{c}{a+t b}\right) & =\frac{z-t x+t^{2} y}{x}+\frac{x-t y+t^{2} z}{y}+\frac{y-t z+t^{2} x}{z} \ & =\left(\frac{z}{x}+\frac{x}{y}+\frac{y}{z}\right)+t^{2}\left(\frac{y}{x}+\frac{z}{y}+\frac{x}{z}\right)-3 t \ & \geqslant 3 \sqrt[3]{\frac{z}{x} \frac{x}{y} \frac{y}{z}}+3 t^{2} \sqrt[3]{\frac{y}{x} \frac{z}{y} \frac{x}{z}}-3 t \ & =3\left(1-t+t^{2}\right)=3 \frac{1+t^{3}}{1+t} \end{aligned} $$
    calc
      _ = (z / x + x / y + y /z) + t^2 * (y / x + z / y + x / z) - 3*t := by
        simp [mul_div_assoc]
        rw [div_self (by positivity), div_self (by positivity), div_self (by positivity)]
        linarith
      _ ≥ 3 + t^2 * 3 - 3 * t := by
        apply sub_le_sub_right
        apply add_le_add (am_gm xpos ypos zpos)
        by_cases t0 : t = 0
        · simp [t0]
        apply (mul_le_mul_left (by positivity)).2
        linarith [am_gm xpos zpos ypos ]
      _ = _ := by
        field_simp
        nlinarith