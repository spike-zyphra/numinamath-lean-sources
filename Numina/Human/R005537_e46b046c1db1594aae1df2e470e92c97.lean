import Mathlib


theorem algebra_608726 {p : ℝ → ℝ} {a : ℕ → ℝ} (ha : ∀ n, a n = 1 ∨ a n = -1)
  (hp : ∀ x, p x = a 6 * x ^ 6 + a 5 * x ^ 5 + a 4 * x ^4 + a 3 * x ^ 3 + a 2 * x ^ 2 + a 1 * x + a 0)
  (hp₂ : p 2 = 27) : p 3 = 439 := by 
  have anbound : ∀ (n : ℕ), a n ≥ -1 := by 
    intro n
    obtain han |ha' := ha n
    linarith
    linarith
  have anbound' : ∀ (n : ℕ), a n ≤  1 := by 
    intro n
    obtain han |ha' := ha n
    linarith
    linarith
  obtain an₅ := anbound 5
  obtain an₄ := anbound 4
  obtain an₃ := anbound 3
  obtain an₂ := anbound 2
  obtain an₁ := anbound 1
  obtain an₀ := anbound 0
  obtain an₅' := anbound' 5
  obtain an₄' := anbound' 4
  obtain an₃' := anbound' 3
  obtain an₂' := anbound' 2
  obtain an₁' := anbound' 1
  obtain an₀' := anbound' 0
  -- The sign of $\pm 2^{n} \pm 2^{n-1} \pm \cdots \pm 2 \pm 1$ is the same as the sign of the $2^{n}$ term. Proof. Without loss of generality, let $2^{n}$ be positive. (We can flip all signs.) Notice that $2^{n} \pm 2^{n-1} \pm$ $2^{n-2} \pm \cdots 2 \pm 1 \geq 2^{n}-2^{n-1}-2^{n-2}-\cdots-2-1=1$, which is positive.
  -- now we step by step to determined the coefficient of all $x^i$. 
  -- Since our desired sum, 27, is positive, the coefficient of $x^{6}$ must be positive.
  have p_sign₆ : a 6 = 1 := by 
    obtain ha₆ | ha₆':= ha 6
    exact ha₆
    by_contra h'
    obtain hp_two := hp 2
    rw [ha₆'] at hp_two
    have ple : p 2 ≤ - 1 := by 
      calc
        _ = -1 * 2 ^ 6 + a 5 * 2 ^ 5 + a 4 * 2 ^ 4 + a 3 * 2 ^ 3 + a 2 * 2 ^ 2 + a 1 * 2 + a 0 := by 
          rw [hp_two]
        _ ≤ -1* 2 ^ 6 +  1 * 2 ^ 5 + 1 * 2 ^ 4 + 1 * 2 ^ 3 + 1 * 2 ^ 2 + 1 * 2 + 1 := by linarith
        _ = -1 := by norm_num
    rw [hp₂] at ple
    linarith
  obtain hp_two := hp 2
  -- Subtracting 64 , we now have that $\pm 2^{5} \pm 2^{4} \pm \ldots \pm 2 \pm 1=-37$, so the sign of $2^{5}$ must be negative.
  have p_sign₅ : a 5 = -1 := by 
    rw [p_sign₆] at hp_two
    have eq_aux : a 5 * 2 ^ 5 + a 4 * 2 ^ 4 + a 3 * 2 ^ 3 + a 2 * 2 ^ 2 + a 1 * 2 + a 0 = - 37 := by 
      calc 
        _ =  (1 * 2 ^ 6 + a 5 * 2 ^ 5 + a 4 * 2 ^ 4 + a 3 * 2 ^ 3 + a 2 * 2 ^ 2 + a 1 * 2 + a 0 )- 64 := by ring
        _ = -37 := by rw [←hp_two, hp₂];norm_num
    obtain ha₅ | ha₅' := ha 5
    by_contra h'
    have pge : a 5 * 2 ^ 5 + a 4 * 2 ^ 4 + a 3 * 2 ^ 3 + a 2 * 2 ^ 2 + a 1 * 2 + a 0 ≥ 1 := by 
      calc 
        _ = 1 * 2 ^ 5 + a 4 * 2 ^ 4 + a 3 * 2 ^ 3 + a 2 * 2 ^ 2 + a 1 * 2 + a 0 := by rw [ha₅]
        _ ≥  1 * 2 ^ 5 + (-1) * 2 ^ 4 + (-1) * 2 ^ 3 + (-1) * 2 ^ 2 + (-1) * 2 + (-1) := by linarith
        _ = 1 := by norm_num
    rw [eq_aux] at pge
    linarith
    exact ha₅'
  -- the same method as above to get the conclusion below.
  have p_sign₄ : a 4 = -1 := by 
    rw [p_sign₆, p_sign₅] at hp_two
    have eq_aux :  a 4 * 2 ^ 4 + a 3 * 2 ^ 3 + a 2 * 2 ^ 2 + a 1 * 2 + a 0 = - 5 := by 
      calc 
        _ =  (1 * 2 ^ 6 + (-1) * 2 ^ 5 + a 4 * 2 ^ 4 + a 3 * 2 ^ 3 + a 2 * 2 ^ 2 + a 1 * 2 + a 0 )- 64 + 32 := by ring
        _ = -5 := by rw [←hp_two, hp₂];norm_num
    obtain ha₅ | ha₅' := ha 4
    by_contra h'
    have pge :  a 4 * 2 ^ 4 + a 3 * 2 ^ 3 + a 2 * 2 ^ 2 + a 1 * 2 + a 0 ≥ 1 := by 
      calc 
        _ = a 4 * 2 ^ 4 + a 3 * 2 ^ 3 + a 2 * 2 ^ 2 + a 1 * 2 + a 0 := by rw [ha₅]
        _ ≥   2 ^ 4 + (-1) * 2 ^ 3 + (-1) * 2 ^ 2 + (-1) * 2 + (-1) := by linarith
        _ = 1 := by norm_num
    rw [eq_aux] at pge
    linarith
    exact ha₅'
  -- -- the same method as above to get the conclusion below.
  have p_sign₃ : a 3 = 1 := by 
    rw [p_sign₆, p_sign₅, p_sign₄] at hp_two
    have eq_aux :   a 3 * 2 ^ 3 + a 2 * 2 ^ 2 + a 1 * 2 + a 0 = 11 := by 
      calc 
        _ =  (1 * 2 ^ 6 + (-1) * 2 ^ 5 + (-1) * 2 ^ 4 + a 3 * 2 ^ 3 + a 2 * 2 ^ 2 + a 1 * 2 + a 0 )- 64 + 32 + 16:= by ring
        _ = 11 := by rw [←hp_two, hp₂];norm_num
    obtain ha₅ | ha₅' := ha 3
    exact ha₅
    by_contra h'
    have pge :   a 3 * 2 ^ 3 + a 2 * 2 ^ 2 + a 1 * 2 + a 0 ≤ - 1 := by 
      calc 
        _ =  a 3 * 2 ^ 3 + a 2 * 2 ^ 2 + a 1 * 2 + a 0 := by rw [ha₅']
        _ ≤  (-1) * 2 ^ 3 + (1) * 2 ^ 2 + (1) * 2 + (1) := by linarith
        _ = -1 := by norm_num
    rw [eq_aux] at pge
    linarith
  -- -- the same method as above to get the conclusion below.
  have p_sign₂ : a 2 = 1 := by 
    rw [p_sign₆, p_sign₅, p_sign₄, p_sign₃] at hp_two
    have eq_aux :  a 2 * 2 ^ 2 + a 1 * 2 + a 0 = 3 := by 
      calc 
        _ =  (1 * 2 ^ 6 + (-1) * 2 ^ 5 + (-1) * 2 ^ 4 + 1* 2 ^ 3 + a 2 * 2 ^ 2 + a 1 * 2 + a 0 )- 64 + 32 + 16 - 8:= by ring
        _ = 3 := by rw [←hp_two, hp₂];norm_num
    obtain ha₅ | ha₅' := ha 2
    exact ha₅
    by_contra h'
    have pge :    a 2 * 2 ^ 2 + a 1 * 2 + a 0 ≤ - 1 := by 
      calc 
        _ =   (-1) * 2 ^ 2 + a 1 * 2 + a 0 := by rw [ha₅']
        _ ≤   (-1) * 2 ^ 2 + (1) * 2 + (1) := by linarith
        _ = -1 := by norm_num
    rw [eq_aux] at pge
    linarith
  -- the same method as above to get the conclusion below.
  have p_sign₁ : a 1 = -1 := by 
    rw [p_sign₆, p_sign₅, p_sign₄, p_sign₃, p_sign₂] at hp_two
    have eq_aux :  a 1 * 2 + a 0 = -1 := by 
      calc 
        _ =  (1 * 2 ^ 6 + (-1) * 2 ^ 5 + (-1) * 2 ^ 4 + 1* 2 ^ 3 + 1 * 2 ^ 2 + a 1 * 2 + a 0 )- 64 + 32 + 16 - 8 - 4:= by ring
        _ = -1 := by rw [←hp_two, hp₂];norm_num
    obtain ha₅ | ha₅' := ha 1
    by_contra h'
    have pge :     a 1 * 2 + a 0 ≥   1 := by 
      calc 
        _ =   1 * 2 + a 0 := by rw [ha₅]
        _ ≥   (1) * 2 + (-1) := by linarith
        _ = 1 := by norm_num
    rw [eq_aux] at pge
    linarith
    exact ha₅'
  -- the same method as above to get the conclusion below.
  have p_sign₀ : a 0  = 1 := by 
    rw [p_sign₆, p_sign₅, p_sign₄, p_sign₃, p_sign₂, p_sign₁] at hp_two
    have eq_aux :   a 0 = 1 := by 
      calc 
        _ =  (1 * 2 ^ 6 + (-1) * 2 ^ 5 + (-1) * 2 ^ 4 + 1* 2 ^ 3 + 1 * 2 ^ 2 + (-1) * 2 + a 0 )- 64 + 32 + 16 - 8 - 4 + 2:= by ring
        _ = 1 := by rw [←hp_two, hp₂];norm_num
    exact eq_aux
  rw [hp 3]
  rw [p_sign₆, p_sign₅, p_sign₄, p_sign₃, p_sign₂, p_sign₁, p_sign₀]
  norm_num
