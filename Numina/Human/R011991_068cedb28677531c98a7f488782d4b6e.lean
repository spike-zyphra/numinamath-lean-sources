import Mathlib

/-
7. Given $0<a<b<c<d<500$, and $a+d=b+c$. Also, $bc-ad=93$.
Then the number of ordered quadruples of integers ( $\dot{a}, b, c$,
$d)$ that satisfy the conditions is . $\qquad$
 -/
theorem algebra_316930 :
    { ⟨a, b, c, d⟩ : ℕ × ℕ × ℕ × ℕ |
    0 < a ∧
    a < b ∧
    b < c ∧
    c < d ∧
    d < 500 ∧
    a + d = b + c ∧
    b * c - a * d = 93
    }.ncard = 870 := by
  --7.870.
  set Quad_ℕ := ℕ × ℕ × ℕ × ℕ
  let s := (Finset.Icc 1 405).map ⟨fun a => (⟨a, a + 1, a + 93, a + 94⟩ : Quad_ℕ), by simp [Function.Injective]⟩
  set t := (Finset.Icc 1 465).map ⟨fun a => (⟨a, a + 3, a + 31, a + 34⟩ : Quad_ℕ), by simp [Function.Injective]⟩
  have : {⟨a, b, c, d⟩ : Quad_ℕ |
      0 < a ∧
      a < b ∧
      b < c ∧
      c < d ∧
      d < 500 ∧
      a + d = b + c ∧
      b * c - a * d = 93
      } = s ∪ t := by
    unfold s t
    ext ⟨a, b, c, d⟩
    constructor
    . intro h
      simp at h ⊢
      /-
      Since $a+d=b+c$, we set $$ (a, b, c, d)=(a, a+x, a+y, a+x+y) \text {, } $$

      where $x$ and $y$ are integers, and $0&lt;x&lt;y$. Then $93=b c-a d$ $$ =(a+x)(a+y)-a(a+x+y)=x y \text {. } $$
       -/
      let x := b - a
      let y := c - a
      have x_pos : 0 < x := by
        omega
      have : x < y := by
        omega
      --have : 93 = x * y := by
      have x_y_eq : x * y = 93 := by
        --unfold x y
        have := h.2.2.2.2.2.2
        rw [
          show b = a + x by omega,
          show c = a + y by omega,
          show d = a + x + y by omega,
        ] at this
        ring_nf at this
        omega
      /-
      Therefore, $(x, y)=(1,93)$ or $(3,31)$. First case $$ (a, b, c, d)=(a, a+1, a+93, a+94) \text {, } $$

      where $a=1,2, \cdots, 405$; Second case $$ (a, b, c, d)=(a, a+3, a+31, a+34) \text {, } $$

      where $a=1,2, \cdots, 465$.
       -/
      --have : (x, y) = (1, 93) ∨ (x, y) = (3, 31) := by
      have : x = 1 ∧ y = 93 ∨ x = 3 ∧ y = 31 := by
        have : x ∣ 93 := by
          exact Dvd.intro y x_y_eq
        have : x ∈ Nat.divisors 93 := by
          refine Nat.mem_divisors.mpr ?_
          constructor
          . exact this
          . decide
        rw [show Nat.divisors 93 = {1, 3, 31, 93} by rfl] at this
        --fin_cases this
        simp at this
        rcases this with x_eq | x_eq | x_eq | x_eq
        . rw [x_eq] at x_y_eq
          left
          omega
        . rw [x_eq] at x_y_eq
          omega
        . exfalso
          have : y = 3 := by
            rw [x_eq] at x_y_eq
            linarith
          linarith
        . exfalso
          rw [x_eq] at x_y_eq
          linarith
      --have : a + x + d < 500
      rcases this with ⟨x_eq, y_eq⟩ | ⟨x_eq, y_eq⟩
      . left
        use a
        constructor
        . omega
        . simp [Prod.mk.injEq, Quad_ℕ]
          omega
      . right
        use a
        constructor
        . omega
        . simp [Prod.mk.injEq, Quad_ℕ]
          omega
    . intro h
      simp at h
      simp
      rcases h with h | h <;>
      . rcases h with ⟨a', a'_range, quadruple_eq⟩
        simp [Prod.mk.injEq, Quad_ℕ] at quadruple_eq
        rcases quadruple_eq with ⟨a'_eq_a, a'_add_eq_b, a'_add_eq_c, a'_add_eq_d⟩
        rw [←a'_eq_a, ←a'_add_eq_b, ←a'_add_eq_c, ←a'_add_eq_d]
        simp
        constructor
        . linarith
        constructor
        . linarith
        constructor
        . ring
        . ring_nf
          omega
  rw [this]
  --rw [Set.encard_coe_eq_coe_finsetCard]
  rw [Set.ncard_coe_Finset]
  -- Thus, the total number of integer quadruples that satisfy the condition is $$ 405+465=870 \text { (sets). } $$
  have : (s ∪ t).card = s.card + t.card := by
    --generalize s_eq : s = s
    --generalize t_eq : t = t
    have : Disjoint s t := by
      unfold s t
      intro u u_ss_s u_ss_t
      simp at u_ss_s u_ss_t /- ⊢ -/
      dsimp
      intro x x_in_u
      simp
      have x_in_s := u_ss_s x_in_u
      have x_in_t := u_ss_t x_in_u
      /-
      apply Finset.disjoint_iff_ne.mpr
      intro x x_in_s y y_in_t a_eq_b
       -/
      rcases x with ⟨a, b, c, d⟩
      --simp [s, t] at x_in_s y_in_t
      simp [s, t] at x_in_s x_in_t
      rcases x_in_s with ⟨a', _, a'_eq_a, a'_add_eq_b, _⟩
      rcases x_in_t with ⟨a'', _, a''_eq_a, eq_b_2, _⟩
      linarith
    exact Finset.card_union_of_disjoint this
  rw [this]
  simp [s, t]
