import Mathlib

/- Beepaal alle viertallen $(a, b, c, d)$ van positieve reële getallen die voldoen aan $a+b+c+d=1$ en

$$
\max \left(\frac{a^{2}}{b}, \frac{b^{2}}{a}\right) \cdot \max \left(\frac{c^{2}}{d}, \frac{d^{2}}{c}\right)=(\min (a+b, c+d))^{4}
$$ -/
/- Bepaal alle viertallen $(a, b, c, d)$ van positieve reële getallen die voldoen aan $a+b+c+d=1$ en

$$
\max \left(\frac{a^{2}}{b}, \frac{b^{2}}{a}\right) \cdot \max \left(\frac{c^{2}}{d}, \frac{d^{2}}{c}\right)=(\min (a+b, c+d))^{4}
$$ -/
theorem algebra_604446 :
  {(a, b, c, d) : ℝ × ℝ × ℝ × ℝ |
    a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧ a + b + c + d = 1 ∧
    max (a ^ 2 / b) (b ^ 2 / a) * max (c ^ 2 / d) (d ^ 2 / c) = (min (a + b) (c + d)) ^ 4
  } = {(1 / 4, 1 / 4, 1 / 4, 1 / 4)} := by

  ext ⟨a, b, c, d⟩
  constructor
  · -- first we show that the equations in the problem implies (a, b, c, d) = (1/4, 1/4, 1/4, 1/4)
    rintro ⟨a_pos, b_pos, c_pos, d_pos, h_sum, h_max_eq⟩

    -- we may well assume a + b ≤ c + d by symmetry
    wlog h_min_eq_left : a + b ≤ c + d
    · have := this c d a b c_pos d_pos a_pos b_pos (by linarith)
        (by rw [min_comm]; linarith) (by linarith)
      rcases this with ⟨rfl, rfl, rfl, rfl⟩
      simp

    -- we need the following inequalities with conditions for equality to hold

    -- 1. rearrangement inequality : a ≤ b, c ≤ d implies a * d + b * c ≤ a * c + b * d
    have lem_mul_add_le_mul_add (a b c d : ℝ) (h1 : a ≤ b) (h2 : c ≤ d) :
      a * d + b * c ≤ a * c + b * d := by
        apply le_of_sub_nonneg
        rw [show a * c + b * d - (a * d + b * c) = (a - b) * (c - d) by ring]
        apply mul_nonneg_of_nonpos_of_nonpos
        all_goals linarith
    -- 1'. if rearrangement inequality is an equality, then a = b or c = d
    have lem_mul_add_le_mul_add' (a b c d : ℝ) (h1 : a ≤ b) (h2 : c ≤ d) :
      a * d + b * c = a * c + b * d → a = b ∨ c = d := by
        intro h
        apply sub_eq_zero.mpr at h
        rw [show a * d + b * c - (a * c + b * d) = (a - b) * (d - c) by ring] at h
        simp at h
        rcases h with h | h
        left; linarith
        right; linarith

    -- 2. max(a, b) ≥ (a + b) / 2
    have lem_add_div_two_le_max (a b : ℝ) : (a + b) / 2 ≤ max a b := by
      by_cases h : a ≤ b
      · rw [max_eq_right h]
        linarith
      · push_neg at h
        rw [max_eq_left (le_of_lt h)]
        linarith

    -- 2'. if max(a, b) = (a + b) / 2 then a = b
    have lem_add_div_two_le_max' (a b : ℝ) : (a + b) / 2 = max a b → a = b := by
      intro h_eq
      by_cases h : a ≤ b
      · rw [max_eq_right h] at h_eq
        linarith
      · push_neg at h
        rw [max_eq_left (le_of_lt h)] at h_eq
        linarith

    -- 3. we know that if a ≤ b and c ≤ d, then a * c ≤ b * d. if the equality holds, then a = b and c = d
    have lem_mul_le_mul_of_le' (a b c d : ℝ) (hb : 0 < b) (hc : 0 < c)
      (h1 : a ≤ b) (h2 : c ≤ d) : a * c = b * d → a = b ∧ c = d := by
        intro h_eq
        constructor
        · by_contra! h
          have : a < b := by exact lt_of_le_of_ne h1 h
          nlinarith
        · by_contra! h
          have : c < d := by exact lt_of_le_of_ne h2 h
          nlinarith

    -- now we start to prove that a = b = c = d = 1 / 4

    -- If $a \geq b$ then $\frac{a}{b} \geq \frac{b}{a}$ and if just $a \leq b$ then $\frac{a}{b} \leq \frac{b}{a}$,
    -- so the sequence $(a, b)$ and the sequence $\left(\frac{a}{b}, \frac{b}{a}\right)$ are equally ordered.
    have lem_eq_order (x y : ℝ) (x_pos : x > 0) (y_pos : y > 0) : x ≥ y → x / y ≥ y / x := by
      intro h
      refine (div_le_div_iff₀ x_pos y_pos).mpr ?mp.a
      rw [← pow_two, ← pow_two]
      refine (pow_le_pow_iff_left₀ ?mp.a.ha ?mp.a.hb ?mp.a.hn).mpr h
      all_goals linarith

    -- The rearrangement inequality now says that
    -- $$ a \cdot \frac{a}{b}+b \cdot \frac{b}{a} \geq a \cdot \frac{b}{a}+b \cdot \frac{a}{b} $$
    have h1 : a * (a / b) + b * (b / a) ≥ a * (b / a) + b * (a / b):= by
      by_cases h : a ≤ b
      · apply lem_mul_add_le_mul_add a b (a / b) (b / a)
        exact h
        exact lem_eq_order b a b_pos a_pos h
      · rw [add_comm]
        nth_rw 2 [add_comm]
        have : b ≤ a := by exact le_of_not_ge h
        apply lem_mul_add_le_mul_add b a (b / a) (a / b)
        exact this
        exact lem_eq_order a b a_pos b_pos this

    -- when the equality holds, we deduce a = b
    have h1' : a * (a / b) + b * (b / a) = a * (b / a) + b * (a / b) → a = b := by
      intro h_eq
      by_cases h : a ≤ b
      · have := lem_mul_add_le_mul_add' a b (a / b) (b / a) h (lem_eq_order b a b_pos a_pos h)
        rcases this h_eq.symm with h_eq' | h_eq'
        · exact h_eq'
        · rw [div_eq_div_iff] at h_eq'
          apply (sq_eq_sq₀ ?H1 ?H2).mp
          all_goals linarith
      · rw [add_comm] at h_eq
        nth_rw 2 [add_comm] at h_eq
        have : b ≤ a := by linarith
        have := lem_mul_add_le_mul_add' b a (b / a) (a / b) this (lem_eq_order a b a_pos b_pos this)
        rcases this h_eq.symm with h_eq' | h_eq'
        · exact h_eq'.symm
        · rw [div_eq_div_iff] at h_eq'
          apply (sq_eq_sq₀ ?H1 ?H2).mp
          all_goals linarith

    -- We can rewrite this as $\frac{a^{2}}{b}+\frac{b^{2}}{a} \geq a+b$.
    rw [
      show a * (a / b) = a ^ 2 / b by ring,
      show b * (b / a) = b ^ 2 / a by ring,
      show a * (b / a) = b by field_simp,
      show b * (a / b) = a by field_simp,
    ] at h1 h1'

    -- If we combine this with $\max \left(\frac{a^{2}}{b}, \frac{b^{2}}{a}\right) \geq$ $\frac{\frac{a^{2}}{b}+\frac{b^{2}}{a}}{2}$, then we see
    -- $$ \max \left(\frac{a^{2}}{b}, \frac{b^{2}}{a}\right) \geq \frac{a+b}{2} . $$
    have h2 : max (a ^ 2 / b) (b ^ 2 / a) ≥ (a + b) / 2 := by
      linarith [lem_add_div_two_le_max (a ^ 2 / b) (b ^ 2 / a)]

    -- again, when the equality holds, we deduce a = b
    have h2' : max (a ^ 2 / b) (b ^ 2 / a) = (a + b) / 2 → a = b := by
      intro h_eq
      have h_eq_1 : max (a ^ 2 / b) (b ^ 2 / a) = ((a ^ 2 / b) + (b ^ 2 / a)) / 2 := by
        linarith [lem_add_div_two_le_max (a ^ 2 / b) (b ^ 2 / a)]
      apply h1'
      linarith

    -- the following lemmas, namely h3, h3', h4, h4' are exactly the same with h1, h1', h2, h2',
    -- we just replace a, b with c, d
    have h3 : c * (c / d) + d * (d / c) ≥ c * (d / c) + d * (c / d):= by
      by_cases h : c ≤ d
      · apply lem_mul_add_le_mul_add c d (c / d) (d / c)
        exact h
        exact lem_eq_order d c d_pos c_pos h
      · rw [add_comm]
        nth_rw 2 [add_comm]
        have : d ≤ c := by exact le_of_not_ge h
        apply lem_mul_add_le_mul_add d c (d / c) (c / d)
        exact this
        exact lem_eq_order c d c_pos d_pos this

    have h3' : c * (c / d) + d * (d / c) = c * (d / c) + d * (c / d) → c = d := by
      intro h_eq
      by_cases h : c ≤ d
      · have := lem_mul_add_le_mul_add' c d (c / d) (d / c) h (lem_eq_order d c d_pos c_pos h)
        rcases this h_eq.symm with h_eq' | h_eq'
        · exact h_eq'
        · rw [div_eq_div_iff] at h_eq'
          apply (sq_eq_sq₀ ?H3 ?H4).mp
          all_goals linarith
      · rw [add_comm] at h_eq
        nth_rw 2 [add_comm] at h_eq
        have : d ≤ c := by linarith
        have := lem_mul_add_le_mul_add' d c (d / c) (c / d) this (lem_eq_order c d c_pos d_pos this)
        rcases this h_eq.symm with h_eq' | h_eq'
        · exact h_eq'.symm
        · rw [div_eq_div_iff] at h_eq'
          apply (sq_eq_sq₀ ?H3 ?H4).mp
          all_goals linarith

    rw [
      show c * (c / d) = c ^ 2 / d by ring,
      show d * (d / c) = d ^ 2 / c by ring,
      show c * (d / c) = d by field_simp,
      show d * (c / d) = c by field_simp,
    ] at h3 h3'

    -- Similarly, we also have $$ \max \left(\frac{c^{2}}{d}, \frac{d^{2}}{d}\right) \geq \frac{c+d}{2} $$
    have h4 : max (c ^ 2 / d) (d ^ 2 / c) ≥ (c + d) / 2 := by
      linarith [lem_add_div_two_le_max (c ^ 2 / d) (d ^ 2 / c)]

    have h4' : max (c ^ 2 / d) (d ^ 2 / c) = (c + d) / 2 → c = d := by
      intro h_eq
      have h_eq_1 : max (c ^ 2 / d) (d ^ 2 / c) = ((c ^ 2 / d) + (d ^ 2 / c)) / 2 := by
        linarith [lem_add_div_two_le_max (c ^ 2 / d) (d ^ 2 / c)]
      apply h3'
      linarith

    -- so $$ \max \left(\frac{a^{2}}{b}, \frac{b^{2}}{a}\right) \cdot \max \left(\frac{c^{2}}{d}, \frac{d^{2}}{c}\right) \geq \frac{(a+b)(c+d)}{4} $$
    have h5 : max (a ^ 2 / b) (b ^ 2 / a) * max (c ^ 2 / d) (d ^ 2 / c) ≥ ((a + b) / 2) * ((c + d) / 2) := by
      apply mul_le_mul
      all_goals linarith

    -- when equality holds, we deduce a = b and c = d
    have h5' : max (a ^ 2 / b) (b ^ 2 / a) * max (c ^ 2 / d) (d ^ 2 / c) = ((a + b) / 2) * ((c + d) / 2) → a = b ∧ c = d := by
      intro h_eq
      have := lem_mul_le_mul_of_le'
        ((a + b) / 2)  (max (a ^ 2 / b) (b ^ 2 / a))
        ((c + d) / 2) (max (c ^ 2 / d) (d ^ 2 / c))
        (by linarith) (by linarith) h2 h4 h_eq.symm
      have ⟨h_ab, h_cd⟩ := this
      constructor
      · exact h2' (id (Eq.symm h_ab))
      · exact h4' (id (Eq.symm h_cd))

    -- we have assumes that $\min (a+b, c+d)=a+b$. Since $a+b+c+d=1$, we have $a+b \leq \frac{1}{2}$.
    have h6 : a + b ≤ 1 / 2 := by linarith
    have h6' : a + b = 1 / 2 → c + d = 1 / 2 := by intros; linarith

    -- therefore, $$\frac{(a+b)(c+d)}{4} \geq \frac{1}{4} \cdot(a+b)^{2}$$
    have h7 : ((a + b) / 2) * ((c + d) / 2) ≥ (a + b) ^ 2 / 4 := by
      calc
        (a + b) ^ 2 / 4 = ((a + b) / 2) * ((a + b) / 2) := by ring
        _ ≤ ((a + b) / 2) * ((c + d) / 2) := by rel [h_min_eq_left]

    -- and when equality holds we deduce a + b = c + d
    have h7' : ((a + b) / 2) * ((c + d) / 2) = (a + b) ^ 2 / 4 → a + b = c + d := by
      rw [show (a + b) ^ 2 / 4 = ((a + b) / 2) * ((a + b) / 2) by ring]
      intro h_eq
      have := lem_mul_le_mul_of_le' ((a + b) / 2) ((a + b) / 2) ((a + b) / 2) ((c + d) / 2)
        (by linarith) (by linarith) (by rfl) (by linarith) h_eq.symm
      have := this.2
      linarith

    -- $$\frac{1}{4} \cdot(a+b)^{2} \geq(a+b)^{2}$$
    have h8 : (a + b) ^ 2 ≤ 1 / 4 := by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num]
      rel [h6]

    -- $$(a+b)^{2} \cdot(a+b)^{2}=(a+b)^{4}$$
    have h9 : (a + b) ^ 2 / 4 ≥ (a + b) ^ 4 := by
      rw [show (a + b) ^ 2 / 4 = (a + b) ^ 2  * (1 / 4) by ring]
      rw [show (a + b) ^ 4 = (a + b) ^ 2 * (a + b) ^ 2 by ring]
      rel [h8]

    -- and when equality holds we deduce a + b = 1 / 2
    have h9' : (a + b) ^ 2 / 4 = (a + b) ^ 4 → a + b = 1 / 2 := by
      rw [show (a + b) ^ 2 / 4 = (a + b) ^ 2  * (1 / 4) by ring]
      rw [show (a + b) ^ 4 = (a + b) ^ 2 * (a + b) ^ 2 by ring]
      intro h_eq
      have : (a + b) ^ 2 > 0 := by
        refine sq_pos_of_pos ?H5
        linarith
      have := lem_mul_le_mul_of_le' ((a + b) ^ 2) ((a + b) ^ 2) ((a + b) ^ 2) (1 / 4)
        this this (by rfl) h8 h_eq.symm
      have := this.2
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num] at this
      apply sq_eq_sq₀ ?H6 ?H7 |>.mp this
      all_goals linarith

    -- We conclude that
    -- $$ \max \left(\frac{a^{2}}{b}, \frac{b^{2}}{a}\right) \cdot \max \left(\frac{c^{2}}{d}, \frac{d^{2}}{c}\right) \geq(a+b)^{4} $$
    have h10 : max (a ^ 2 / b) (b ^ 2 / a) * max (c ^ 2 / d) (d ^ 2 / c) ≥ (a + b) ^ 4 := by
      linarith

    have h_min := min_eq_left h_min_eq_left
    rw [h_min] at h_max_eq

    -- Given that equality holds here, equality must hold everywhere in the above steps.
    -- in particular, the following is an equality
    have : (a + b) ^ 2 / 4 = (a + b) ^ 4 := by linarith
    -- from what we have shown we deduce a + b = 1 / 2 and c + d = 1 / 2
    have h_ab := h9' this
    have h_cd := h6' h_ab

    -- also, the following equality holds, and we deduce a = b and c = d
    have : max (a ^ 2 / b) (b ^ 2 / a) * max (c ^ 2 / d) (d ^ 2 / c) = (a + b) / 2 * ((c + d) / 2) := by linarith
    have ⟨h_a_eq_b, h_c_eq_d⟩ := h5' this

    -- this gives us a = b = c = d = 1 / 4.
    have : a = 1 / 4 := by
      rw [← h_a_eq_b, ← mul_two, show (1/2 : ℝ) = (1/4) * 2 by norm_num] at h_ab
      refine eq_one_div_of_mul_eq_one_left ?_
      linear_combination 2 * h_ab
    rw [this]
    have : b = 1 / 4 := by
      rw [h_a_eq_b, ← mul_two, show (1/2 : ℝ) = (1/4) * 2 by norm_num] at h_ab
      refine eq_one_div_of_mul_eq_one_left ?_
      linear_combination 2 * h_ab
    rw [this]
    have : c = 1 / 4 := by
      rw [← h_c_eq_d, ← mul_two, show (1/2 : ℝ) = (1/4) * 2 by norm_num] at h_cd
      refine eq_one_div_of_mul_eq_one_left ?_
      linear_combination 2 * h_cd
    rw [this]
    have : d = 1 / 4 := by
      rw [h_c_eq_d, ← mul_two, show (1/2 : ℝ) = (1/4) * 2 by norm_num] at h_cd
      refine eq_one_div_of_mul_eq_one_left ?_
      linear_combination 2 * h_cd
    rw [this]

    simp
  · -- On the other hand, Substituting (1/4, 1/4, 1/4, 1/4) into the given equality shows that both sides are $\frac{1}{16}$, so this quadruple satisfies the equality.
    intro h
    simp at h
    rcases h with ⟨rfl, rfl, rfl, rfl⟩
    repeat constructor; norm_num
    norm_num
