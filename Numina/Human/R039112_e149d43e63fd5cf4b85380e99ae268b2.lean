import Mathlib

/- 226. Equation containing fractions. Solve the equation

$$
\frac{x-a}{b}+\frac{x-b}{a}=\frac{b}{x-a}+\frac{a}{x-b}
$$ -/
theorem algebra_270633 {a b x : ℝ} (ha: a ≠ 0) (hb: b ≠ 0) (hxb : x ≠ b) (hxa : x ≠ a) (hab: a + b ≠ 0) :
    (x - a) / b + (x - b) / a = b / (x - a) + a / (x - b) ↔
    x = 0 ∨ x = a + b ∨ x = (a ^ 2 + b ^ 2) / (a + b) := by

    -- Firstly we show the denominators are not zero
    have ne_xa: x - a ≠ 0 := by
      by_contra! no
      replace no: x = a := by
        linarith
      simp [no] at hxa
    have ne_xb: x - b ≠ 0 := by
      by_contra! no
      replace no: x = b := by
        linarith
      simp [no] at hxb
    constructor

    -- forward direction
    . intro h
      set m:= (x - a) / b with hm
      set n:= (x - b) / a with hn
      have vm: b / (x - a) = 1 / m := by
        field_simp [ne_xa, ha, hm]
      have vn: a / (x - b) = 1 / n := by
        field_simp [ne_xb, hb, hn]
      simp [vm, vn] at h
      field_simp at h
      replace h: (m + n) * (m * n - 1) = 0 := by  --factor the equation
        nlinarith
      simp at h
      rcases h with h | h
      -- case 1: m + n = 0
      . simp [hm, hn] at h
        field_simp at h
        right
        right
        field_simp
        nlinarith
      -- case 2: m * n - 1 = 0
      . simp [hm, hn] at h
        field_simp at h
        ring_nf at h
        rw [show -(x * a) - x * b + x ^ 2 = x * (x - (a + b)) by ring] at h
        simp at h
        rcases h with h | h
        . left
          simp [h]
        . right
          left
          linarith

    -- backward direction
    . intro h
      rcases h with h | h | h
      -- case 1: x = 0
      . simp [h]
        have o1: -a ≠ 0 := by
          by_contra! no
          replace no: a = 0 := by
            linarith
          simp [no] at ha
        have o2: -b ≠ 0 := by
          by_contra! no
          replace no: b = 0 := by
            linarith
          simp [no] at hb
        field_simp
        ring
      -- case 2: x = a + b
      . simp [h]
      -- case 3: x = (a ^ 2 + b ^ 2) / (a + b), it's a little bit tricky
      . simp [h]
        field_simp
        have o1: (a ^ 2 + b ^ 2 - (a + b) * a) ≠ 0 := by -- we need to show the denominators are not zero, so that we can field_simp
          by_contra! no
          ring_nf at no
          rw [show -(a * b) + b ^ 2 = b * (b - a) by ring] at no
          simp at no
          rcases no with o | o
          . tauto
          . replace o: b = a := by
              linarith
            simp [o] at h
            ring_nf at h
            have o1: -a ≠ 0 := by
              by_contra! no
              replace no: a = 0 := by
                linarith
              simp [no] at ha
            have j: a ^ 2 * a⁻¹ = a := by field_simp; ring
            rw [j] at h
            tauto
        have o2: (a ^ 2 + b ^ 2 - (a + b) * b) ≠ 0 := by
          by_contra! no
          ring_nf at no
          rw [show -(a * b) + a ^ 2 = a * (a - b) by ring] at no
          simp at no
          rcases no with o | o
          . tauto
          . replace o: a = b := by
              linarith
            simp [o] at h
            ring_nf at h
            have o1: -b ≠ 0 := by
              by_contra! no
              replace no: b = 0 := by
                linarith
              simp [no] at hb
            have j: b ^ 2 * b⁻¹ = b := by field_simp; ring
            rw [j] at h
            tauto
        field_simp [o1, o2]
        ring