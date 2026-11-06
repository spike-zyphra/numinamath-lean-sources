import Mathlib


/- Let $X$ be a finite set of positive integers with at least two elements. If for any two integers $a, b \in X$ such that $a>b$, the integer $\frac{b}{a-b}$ (which implies $a-b$ divides $b$) is also an element of $X$, show that $X$ must be of the form $\{j, j+1\}$ for some positive integer $j$. -/
theorem number_theory_635633 {X : Finset ℕ} (Xpos: ∀ x ∈ X, 0 < x)
  (X_card: 2 ≤ X.card):
  (∀a b, a ∈ X → b ∈ X → a > b → (a-b ∣ b ∧ b/(a-b) ∈ X)) ↔
  (∃ j:ℕ, 0 < j ∧ X = {j, j+1}) := by

  constructor

  · intro hX
    change 1 < X.card at X_card
    -- suppose x is the minimum of X.
    have: X.Nonempty := by
      refine Finset.card_pos.mp ?_
      exact Nat.zero_lt_of_lt X_card
    rcases (Finset.min_of_nonempty this) with ⟨x, x_min⟩
    -- suppose y is the second smallest.
    replace: (X.erase x).Nonempty := by
      refine Finset.card_pos.mp ?_
      rw [Finset.card_erase_of_mem (Finset.mem_of_min x_min)]
      exact Nat.zero_lt_sub_of_lt X_card
    rcases (Finset.min_of_nonempty this) with ⟨y, y_min⟩
    have x_mem := Finset.mem_of_min x_min
    have y_mem := Finset.mem_of_mem_erase (Finset.mem_of_min y_min)
    -- by our definition, x < y, and x,y are both in X.
    have xlty: x < y := by
      apply lt_of_le_of_ne ?_ ?_
      · exact Finset.min_le_of_eq y_mem x_min
      · have := Finset.mem_of_min y_min
        rintro heq
        simp [heq] at this
    -- then y-x divide x, and x/(y-x) is in the set
    replace := hX y x y_mem x_mem xlty
    -- we claim it must be the case y-x = 1, otherwise x/(y-x) < x.
    replace: y - x = 1 := by
      by_contra! h1
      have h2: x / (y-x) < x := by
        refine Nat.div_lt_self (Xpos x x_mem) ?_
        omega
      have h3: x ≤ x/(y-x) := Finset.min_le_of_eq this.right x_min
      linarith only [h2, h3]
    -- therefore we claim X is {x,x+1}
    use x,(Xpos x x_mem)
    ext z
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hz
      suffices h1: ¬ z > x+1 by
        push_neg at h1
        have h2: x ≤ z := Finset.min_le_of_eq hz x_min
        omega
      by_contra! h1
      have h2 := hX z x hz x_mem (by linarith only [h1])
      -- if some z ≥ x+2 is in X, then x/(z-x) ≤ x/2 is in X.
      -- contradicts minimality of x.
      have h3: x/(z-x) < x := by
        refine Nat.div_lt_self (Xpos x x_mem) ?_
        exact Nat.lt_sub_iff_add_lt'.mpr h1
      absurd h3
      push_neg
      apply Finset.min_le_of_eq h2.right x_min
    · rintro (zeq | zeq)
      · rwa [zeq]
      · replace: y = x+1 := by omega
        rwa [zeq, ← this]

  · rintro ⟨j, jpos, Xeq⟩
    rw [Xeq]
    simp only [Finset.mem_insert, Finset.mem_singleton, gt_iff_lt]
    intro a b ha hb blta
    replace ha: a = j+1 := by
      rcases hb with hb | hb
      <;> rcases ha with ha | ha
      any_goals simp [ha, hb] at blta
      any_goals simp [ha]
    replace hb: b = j := by
      rcases hb with hb | hb
      · exact hb
      · simp [ha, hb] at blta
    simp [ha, hb]