import Mathlib


/- . Trouver tous les entiers naturels $\mathrm{k}>0$ tels que l'équation en $x$ et y :

$$
x(x+k)=y(y+1)
$$

ait une solution en entiers strictement positifs. -/
theorem number_theory_607464 (k : ℕ) (kpos: k > 0) :
    (∃ x y : ℤ, x > 0 ∧ y > 0 ∧ x * (x + k) = y * (y + 1)) ↔ k = 1 ∨ k ≥ 4 := by

  -- cases on k is odd or even.
  rcases (Nat.even_or_odd' k) with ⟨k, (rfl | rfl)⟩

  · -- k even case.
    push_cast
    -- equation x(x+2k) = y(y+1) is equivalent to
    -- (2x-2y+2k-1)(2x+2y+2k+1) = 4k^2-1
    have h1 {x y: ℤ}: x*(x+(2*k)) = y*(y+1) ↔
      (2*x-2*y+2*k-1)*(2*x+2*y+2*k+1) = 4*k^2-1 := by
      constructor <;> intro h <;> linarith only [h]
    constructor

    · -- given equation holds, decide k.
      rintro ⟨x,y, hx, hy, heq⟩

      -- suffices to exclude k=1 case.
      have kne1: k ≠ 1 := by
        rw [h1] at heq
        rintro keq
        -- suppose on the contrary, the equation turns to
        -- (2x-2y+1) (2x+2y+3) = 3.
        -- both factor must > 0.
        have h2: 2*x-2*y+2*k-1 > 0 := by
          have: (0:ℤ) < 4*k^2-1 := by
            simp [keq]
          rw [← heq] at this
          apply pos_of_mul_pos_left this ?_
          rw [keq]
          linarith only [hx, hy]
        -- then first factor ≥ 1.
        replace h2: 2*x-2*y+2*k-1 ≥ 1 := by exact h2
        -- which forces second factor ≤ 3.
        have h3: 2*x+2*y+2*k+1 ≤ 4*k^2-1 := by
          rw [← heq]
          refine (le_mul_iff_one_le_left ?_).mpr h2
          rw [keq]
          linarith only [hx, hy]
        -- but it's impossible, since 2x+2y > 0.
        absurd h3
        push_neg
        rw [keq]
        norm_num
        linarith only [hx, hy]

      -- then k ≥ 2, or, 2k ≥ 4.
      right; omega

    · -- given 2k ≥ 4, find a solution.
      rintro (hk | hk)
      · -- impossible for 2k=1.
        omega
      · -- 2k ≥ 4, then k > 1. k>0 and k-1 > 0.
        have hk1: k > (0:ℤ) := by omega
        have hk2: k - 1 > (0:ℤ) := by omega
        -- find solution for (2x-2y+2k-1)(2x+2y+2k+1) = (2k-1)(2k+1).
        -- we can choose x = k(k-1), y = (k+1)(k-1)
        use (k*(k-1):ℤ),((k+1)*(k-1):ℤ)
        have hx: (0:ℤ) < k*(k-1) := Int.mul_pos hk1 hk2
        have hy: (0:ℤ) < (k+1)*(k-1) := Int.mul_pos (by simp) hk2
        refine ⟨hx, hy, ?_⟩
        rw [h1]
        ring

  · -- k odd case.
    -- the equation turns to (x-y+k)(x+y+k+1) = k(k+1)
    have h1 {x y:ℤ}: x*(x+(2*k+1)) = y*(y+1) ↔
      (x-y+k)*(x+y+k+1) = k*(k+1) := by
      constructor <;> intro h <;> linarith only [h]

    constructor

    · -- given equation holds, decide k.
      rintro ⟨x,y, hx, hy, heq⟩
      push_cast at heq

      -- if k = 0, 2k+1 = 1.
      by_cases hk: k = 0
      · left; simp [hk]
      -- now we have 0 < k.
      replace hk: (0:ℤ) < k := by omega

      -- suffices to exclude k=1 case.
      have kne1: k ≠ 1 := by
        rintro keq
        rw [h1] at heq
        -- (x-y+1)(x+y+2) = 2 is impossible.
        -- since first factor ≥ 1, and second factor ≥ 2.
        have h2: x-y+k > 0 := by
          have: k*(k+1) > (0:ℤ) := by positivity
          rw [← heq] at this
          apply pos_of_mul_pos_left this (by positivity)
        replace h2: x-y+k ≥ 1 := by exact h2
        have h3: x+y+k+1 ≤ k*(k+1) := by
          rw [← heq]
          refine (le_mul_iff_one_le_left ?_).mpr h2
          positivity
        -- but x+y+2 > 2, contradiction.
        absurd h3
        push_neg
        simp only [keq, Nat.cast_one, Int.reduceAdd, one_mul]
        linarith only [hx, hy]

      -- k > 0 and k ≠ 1, then k ≥ 2. therefore 2k+1 ≥ 4.
      replace hk: k ≥ 2 := by omega
      right; linarith only [hk]

    · -- given k, find solution of x,y.
      rintro (hk | hk)

      · -- when 2k+1=1, find solution for x(x+1) = y(y+1).
        -- we may just choose x=y=1.
        rw [hk]
        use 1,1
        norm_num

      · -- find solution of (x-y+k)(x+y+k+1) = k(k+1).
        -- we may choose x = k(k-1)/2, y = (k-1)(k+2)/2
        use ((k*(k-1))/2: ℤ), (((k-1)*(k+2))/2:ℤ)
        push_cast
        rw [h1]
        -- 2 divide k(k-1) and (k-1)(k+2)
        have h2: (2:ℤ) ∣ k*(k-1:ℤ) := by
          rw [← even_iff_two_dvd]
          rcases (Int.even_or_odd k) with kk | kk
          <;> apply Int.even_mul_pred_self
        have h3: (2:ℤ) ∣ (k-1:ℤ)*(k+2) := by
          rw [← even_iff_two_dvd]
          rcases (Int.even_or_odd k) with kk | kk
          · refine Even.mul_left ?_ _
            exact Even.add kk (Int.even_iff.mpr rfl)
          · refine Even.mul_right ?_ _
            refine Int.even_sub_one.mpr ?_
            exact Int.not_even_iff_odd.mpr kk
        -- some calculations.
        qify at hk ⊢
        have hk1: (0:ℚ) < k-1 := by
          linarith only [hk]
        have hk2: (0:ℚ) < k := by
          linarith only [hk1]
        rw [Int.cast_div h2 (by norm_num),
        Int.cast_div h3 (by norm_num)]
        simp only [Int.cast_mul, Int.cast_natCast, Int.cast_sub,
        Int.cast_one, Int.cast_ofNat, Nat.ofNat_pos,
        div_pos_iff_of_pos_right, Int.cast_add]
        refine ⟨?_, ?_, ?_⟩
        · positivity
        · apply mul_pos hk1 (by linarith only [hk2])
        · ring