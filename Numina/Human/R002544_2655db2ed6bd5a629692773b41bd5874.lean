import Mathlib

open Real

/-- The number of distinct pairs of integers $(x, y)$ such that $0 < x < y$ and
$\sqrt{1984}=\sqrt{x}+\sqrt{y}$ is

$\mathrm{(A) \ }0 \qquad \mathrm{(B) \ }1 \qquad \mathrm{(C) \ } 3 \qquad \mathrm{(D) \ }4
\qquad \mathrm{(E) \ } 7$ -/
theorem number_theory_95116 :
    {(x, y) : ℕ × ℕ | 0 < x ∧ x < y ∧ √1984 = √x + √y}.ncard = 3 := by

  -- Let $s$ be the set of all pairs of positive integers $(x, y)$ such that $0 < x < y$ and
  -- $\sqrt{1984} = \sqrt{x} + \sqrt{y}$.
  set s := {(x, y) : ℕ × ℕ | 0 < x ∧ x < y ∧ √1984 = √x + √y}

  -- Notice that $1984 = 8^2 \cdot 31$. Therefore, $\sqrt{1984} = 8 \sqrt{31}$.
  have : √1984 = 8 * √31 := by
    calc _ = √(8^2 * 31) := by congr; norm_num
         _ = _ := by simp

  -- Let $t$ be the set of all pairs of positive integers $(a, b)$ such that $0 < a < b$ and
  -- $a + b = 8$.
  let t := {(a, b) : ℕ × ℕ | 0 < a ∧ a < b ∧ a + b = 8}

  -- Let $f$ be the function that maps $(a, b)$ to $(31a^2, 31b^2)$.
  let f : ℕ × ℕ → ℕ × ℕ := fun ⟨a, b⟩ ↦ (31 * a^2, 31 * b^2)

  -- We claim that $f$ is a bijection from $t$ to $s$, therefore it suffices to show that $t$ has
  -- $3$ elements.
  suffices t.ncard = 3 from ?_

  -- Let's show that our claim.
  · rw [←this]
    symm
    apply Set.ncard_congr (fun p _ ↦ f p)

    -- Firstly, we need to show that $f$ maps $t$ to $s$. However, this is almost trivial from
    -- the definition of $f$.
    · rintro ⟨a, b⟩ ⟨ha, hab1, hab2⟩
      refine ⟨?_, ?_, ?_⟩
      · positivity
      · gcongr
      -- Substituting $x = 31 a^2$ and $y = 31 b^2$ into the equation, we get
      -- $\sqrt{31 a^2} + \sqrt{31 b^2} = \sqrt{31}(a + b) = 8 \sqrt{31} = \sqrt{1984}$.
      · rify at hab2
        simp
        rw [←mul_add, mul_comm, ‹√1984 = 8 * √31›]
        simp [hab2]


    -- Secondly, we need to show that $f$ is injective. This is very easy because squaring and
    -- multiplying by $31$ are both injective operations.
    · rintro ⟨a, b⟩ ⟨a', b'⟩ _ _ h
      simp [f] at h
      simp [h]

    -- Lastly, we need to show that $f$ is surjective. This is harder. Let $(x, y)$ be an element of
    -- $s$. Then, $\sqrt{1984} = \sqrt{x} + \sqrt{y}$.
    · rintro ⟨x, y⟩ ⟨hx, hxy1, hxy2⟩

      -- Rearranging, and then squaring, we get $y = 1984 - 16 \sqrt{31x} + x$.
      have : √y = √1984 - √x := by linarith
      have : (y : ℝ) = 1984 - 16 * √(31 * x) + x := by
        calc _ = (√y)^2 := by simp
             _ = (√1984 - √x)^2 := by rw [this]
             _ = (√1984)^2 - 2 * √1984 * √x + (√x)^2 := by ring
             _ = 1984 - 2 * √1984 * √x + x := by simp
             _ = 1984 - 2 * (8 * √31) * √x + x := by congr
             _ = 1984 - 16 * (√31 * √x) + x := by ring
             _ = _ := by simp

      -- This means that $\sqrt{31 x} = 1984 + x - y$ which is rational.
      have : ∃ q : ℚ , √(31 * x) = q := by
        use (1984 + x - y) / 16
        rify
        nlinarith
      have : ¬ Irrational (√(((31 * x) : ℕ) : ℚ)) := by
        simp [-sqrt_mul', -sqrt_mul, Irrational]
        convert this using 2
        rw [Eq.comm]

      -- A square root of a natural number is either an integer or irrational. Therefore, $\sqrt{31 x}$
      -- is an integer.
      rw [irrational_sqrt_rat_iff] at this
      simp [-Nat.cast_mul] at this
      norm_cast at this

      -- Let $a'$ be this integer.
      set a' := (31 * x).sqrt

      -- 31 divides $a'^2$ and 31 is prime, so $31$ divides $a'$.
      have : 31 ∣ a' := by
        apply Nat.Prime.dvd_of_dvd_pow (n := 2) (by norm_num)
        use x
        convert this using 1
        ring

      -- Write $a' = 31 a$ for some integer $a$.
      rcases this with ⟨a, ha'a⟩

      -- Then, $x = 31 a^2$.
      have hxa : x = 31 * a^2 := by nlinarith only [ha'a, this]

      -- Now, it will even easier to see that $y = 31 b^2$ for some integer $b$.
      -- First, rewrite our original by substituting $x = 31 a^2$. We get $√y = (8 - a) √31$.
      have : √y = (8 - a) * √31 := by
        calc _ = √1984 - √x := by linarith
             _ = √1984 - √(31 * a^2) := by simp [hxa]
             _ = √1984 - a * √31 := by simp [mul_comm]
             _ = 8 * √31 - a * √31 := by congr
             _ = (8 - a) * √31 := by ring

      -- Notice that $a ≤ 8$ because $\sqrt{y}$ is positive. Therefore, we can safely divide by
      -- $8 - a$.
      have ha : a ≤ 8 := by
        rify
        by_contra! ha
        suffices (0:ℝ) < 0 by norm_num at this
        calc 0 < √y := by rw [Real.sqrt_pos]; norm_cast; linarith
             _ = (8 - a) * √31 := by assumption
             _ ≤ 0 := by nlinarith [(by norm_num : 0 < √31)]

      -- Squaring, we get $y = 31 b^2$ where $b = 8 - a$.
      let b := 8 - a
      have hyb : y = 31 * b^2 := by
        rify
        calc _ = (√y)^2 := by simp
             _ = ((8 - a) * √31)^2 := by rw [this]
             _ = (8 - a)^2 * 31 := by simp [mul_pow]
             _ = _ := by simp [b, mul_comm, ha]

      -- By the definitions of $a$ and $b$, it is clear that $(a, b)$ is an element of $t$ and
      -- $f(a, b) = (x, y)$.
      refine ⟨⟨a, b⟩, ⟨by nlinarith, by nlinarith, by omega⟩, ?_⟩
      simp [f, hxa, hyb]

  clear! s f this
  -- Now, we need to show that $t$ has $3$ elements. $t$ is a very simple set, so this is easy.
  -- Actually, we claim that $t = \{(1, 7), (2, 6), (3, 5)\}$.
  suffices t = {(1, 7), (2, 6), (3, 5)} from by simp [this]

  ext ⟨a, b⟩
  constructor
  -- For the left to write direction, let $(a, b) \in t$.
  · rintro ⟨ha, hab1, hab2⟩
    -- The sum of $a$ and $b$ is $8$ but $a < b$. Therefore, $a < 4$.
    have : a < 4 := by omega

    -- For each possible value of $a$, we can determine $b$.
    interval_cases a <;> simp <;> omega

  -- For the right to left direction, we will show, one by one, that $(1, 7)$, $(2, 6)$, and $(3, 5)$
  -- are elements of $t$. However, this is just a very simple calculation.
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp [t]