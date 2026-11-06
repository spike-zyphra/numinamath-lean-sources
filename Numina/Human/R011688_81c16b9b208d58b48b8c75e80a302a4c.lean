import Mathlib
set_option maxHeartbeats 400000

/- 8 Given that $a, b, c, d, e$ are positive numbers, and $a b c d e=1$, prove:
$$\begin{array}{c}
\frac{a+a b c}{1+a b+a b c d}+\frac{b+b c d}{1+b c+b c d e}+\frac{c+c d e}{1+c d+c d e a}+ \\
\frac{d+d e a}{1+d e+d e a b}+\frac{e+e a b}{1+e a+e a b c} \geqslant \frac{10}{3}
\end{array}$$ -/
theorem inequalities_603754 (a b c d e : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (hd : 0 < d)
    (he : 0 < e)
    (h : a * b * c * d * e = 1) :
    10 / 3 ≤
    (a + a * b * c) / (1 + a * b + a * b * c * d) +
    (b + b * c * d) / (1 + b * c + b * c * d * e) +
    (c + c * d * e) / (1 + c * d + c * d * e * a) +
    (d + d * e * a) / (1 + d * e + d * e * a * b) +
    (e + e * a * b) / (1 + e * a + e * a * b * c) := by

    -- Let $a=\frac{y}{x}, b=\frac{z}{y}, c=\frac{u}{z}, d=\frac{v}{u}, e=\frac{x}{v}, x, y, z, u, v \in \mathbf{R}^{+}$
    let x := a * b * c * d * e
    let y := a
    let z := a * b
    let u := a * b * c
    let v := a * b * c * d

    have xpos : x > 0 := by positivity
    have ypos : y > 0 := by positivity
    have zpos : z > 0 := by positivity
    have upos : u > 0 := by positivity
    have ypos : v > 0 := by positivity

    have a_eq : a = y / x := by field_simp [x, y, z, u, v, h]
    have b_eq : b = z / y := by field_simp [x, y, z, u, v, h]
    have c_eq : c = u / z := by field_simp [x, y, z, u, v, h]
    have d_eq : d = v / u := by field_simp [x, y, z, u, v, h]
    have e_eq : e = x / v := by field_simp [x, y, z, u, v, h]; rw [← h]; ring

    -- then the original inequality is equivalent to
    -- $\frac{u+y}{x+z+v}+\frac{z+v}{x+y+u}+\frac{x+u}{y+z+v}+\frac{y+v}{x+z+u}+$ $\frac{x+z}{y+u+v} \geqslant \frac{10}{3}$
    have : (a + a * b * c) / (1 + a * b + a * b * c * d) = (u + y) / (x + z + v) := by
      field_simp
      rw [a_eq, b_eq, c_eq, d_eq]
      field_simp
      ring
    rw [this]

    have : (b + b * c * d) / (1 + b * c + b * c * d * e) = (z + v) / (x + y + u) := by
      field_simp
      rw [e_eq, b_eq, c_eq, d_eq]
      field_simp
      ring
    rw [this]

    have : (c + c * d * e) / (1 + c * d + c * d * e * a) = (x + u) / (y + z + v) := by
      field_simp
      rw [e_eq, a_eq, c_eq, d_eq]
      field_simp
      ring
    rw [this]

    have : (d + d * e * a) / (1 + d * e + d * e * a * b) = (y + v) / (x + z + u) := by
      field_simp
      rw [e_eq, a_eq, b_eq, d_eq]
      field_simp
      ring
    rw [this]

    have : (e + e * a * b) / (1 + e * a + e * a * b * c) = (x + z) / (y + u + v) := by
      field_simp
      rw [e_eq, a_eq, b_eq, c_eq]
      field_simp
      ring
    rw [this]

    have : (u + y) / (x + z + v) = (x + y + z + u + v) / (x + z + v) - 1 := by
      field_simp
      ring
    rw [this]

    have : (z + v) / (x + y + u) = (x + y + z + u + v) / (x + y + u) - 1 := by
      field_simp
      ring
    rw [this]

    have : (x + u) / (y + z + v) = (x + y + z + u + v) / (y + z + v) - 1 := by
      field_simp
      ring
    rw [this]

    have : (y + v) / (x + z + u) = (x + y + z + u + v) / (x + z + u) - 1 := by
      field_simp
      ring
    rw [this]

    have : (x + z) / (y + u + v) = (x + y + z + u + v) / (y + u + v) - 1 := by
      field_simp
      ring
    rw [this]

    have : ((x + y + z + u + v) / (x + z + v) - 1) + ((x + y + z + u + v) / (x + y + u) - 1) + ((x + y + z + u + v) / (y + z + v) - 1) + ((x + y + z + u + v) / (x + z + u) - 1) + ((x + y + z + u + v) / (y + u + v) - 1) = (x + y + z + u + v) * (1 / (x + z + v) + 1 / (x + y + u) + 1 / (y + z + v) + 1 / (x + z + u) + 1 / (y + u + v)) - 5 := by
      ring
    rw [this]

    -- Adding 5 to both sides, and then multiplying by 3, the above inequality is equivalent to
    -- $$\begin{array}{l} \quad 3(x+y+z+u+v) \cdot\left(\frac{1}{x+z+v}+\frac{1}{x+y+u}+\frac{1}{y+z+v}+\frac{1}{x+z+u}+\right. \ \left.\frac{1}{y+u+v}\right) \geqslant 25 \end{array}$$
    suffices h : 3 * (x + y + z + u + v) * (1 / (x + z + v) + 1 / (x + y + u) + 1 / (y + z + v) + 1 / (x + z + u) + 1 / (y + u + v)) ≥ 25 by
      linarith

    have : 3 * (x + y + z + u + v) = (x + z + v) + (x + y + u) + (y + z + v) + (x + z + u) + (y + u + v) := by ring
    rw [this]

    let f : Fin 5 → ℝ := fun i ↦ match i with
      | 0 => (x + z + v)
      | 1 => (x + y + u)
      | 2 => (y + z + v)
      | 3 => (x + z + u)
      | 4 => (y + u + v)

    let g : Fin 5 → ℝ := fun i ↦ match i with
      | 0 => 1 / (x + z + v)
      | 1 => 1 / (x + y + u)
      | 2 => 1 / (y + z + v)
      | 3 => 1 / (x + z + u)
      | 4 => 1 / (y + u + v)

    have : (x + z + v + (x + y + u) + (y + z + v) + (x + z + u) + (y + u + v)) *
    (1 / (x + z + v) + 1 / (x + y + u) + 1 / (y + z + v) + 1 / (x + z + u) + 1 / (y + u + v)) = (∑ i, f i) * (∑ i, g i) := by
      unfold f g
      iterate 10 rw [Fin.sum_univ_succ]
      simp [Fin.succ]
      ring
    rw [this]

    let r : Fin 5 → ℝ := fun i ↦ f i * g i
    have h_r_eq_1 : ∀ i, r i = 1 := by
      intro i
      unfold r
      match i with
      | 0 => unfold f g; dsimp; field_simp
      | 1 => unfold f g; dsimp; field_simp
      | 2 => unfold f g; dsimp; field_simp
      | 3 => unfold f g; dsimp; field_simp
      | 4 => unfold f g; dsimp; field_simp

    have : 25 = (∑ i, r i) ^ 2 := by
      simp only [h_r_eq_1, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_ofNat, mul_one]
      norm_num
    rw [this]

    -- Using the Cauchy inequality, the above inequality is obvious.
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul

    · intro i _
      fin_cases i
      all_goals
        dsimp [f]
        positivity
    · intro i _
      fin_cases i
      all_goals
        dsimp [g]
        positivity
    · intro i _
      have : f i * g i = r i := by unfold r; rfl
      rw [this]
      rw [h_r_eq_1]
      norm_num
