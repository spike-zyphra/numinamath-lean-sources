import Mathlib

/- Find all prime numbers $p$ such that there exist positive integers $x, y$ that satisfy the relation $x\left(y^{2}-p\right)+y\left(x^{2}-p\right)=5 p$. -/
theorem number_theory_604390 (p : ℕ) (hp : Nat.Prime p) :
  (∃ x y : ℤ, x > 0 ∧ y > 0 ∧ x * (y ^ 2 - p) + y * (x ^ 2 - p) = 5 * p) ↔ p = 2 ∨ p = 3 ∨ p = 7 := by
  constructor
  intro hxy
  rcases hxy with ⟨x, y, hx, hy, hxy⟩
  -- The given equation is equivalent to $(x+y)(x y-p)=5 p$.
  have : x * (y ^ 2 - p) + y * (x ^ 2 - p) = (x + y) * (x * y - p) := by ring
  rw [this] at hxy
  -- Obviously $x+y \geq 2$.
  have hx' : 1 ≤ x := hx
  have hy' : 1 ≤ y := hy
  have hxy' : 2 ≤ x + y := by linarith
  -- We will consider the following three cases:
  have h1 : (x + y) ∣ 5 * p := by
    rw [← hxy] ; exact Int.dvd_mul_right (x + y) (x * y - ↑p)
  have : ∃ t : ℕ , t = x + y := by refine CanLift.prf (x + y) ?_ ;linarith
  rcases this with ⟨t, ht⟩
  have h2 : t ∣ 5 * p := by
    rw [← ht] at h1 ; exact Int.ofNat_dvd.mp h1
  apply Nat.dvd_mul.mp at h2
  rcases h2 with ⟨d1,d2,hd1,hd2,hd1d2⟩
  rcases (Nat.dvd_prime Nat.prime_five).mp hd1 with h1'|h1'
  rcases (Nat.dvd_prime hp).mp hd2 with h2|h2
  · simp [← ht,← hd1d2,h1',h2] at hxy'
  -- Case 2: $x+y=p$ and $x y=p+5$.
  · simp [← hd1d2,h1',h2] at ht
    have : p ≠ 0 := by exact Nat.Prime.ne_zero hp
    simp [← ht,mul_comm,this] at hxy
    -- We have $x y-x-y=5$ or $(x-1)(y-1)=6$ which implies $(x, y) \in{(2,7) ;(3,4) ;(4,3) ;(7,2)}$.
    have hxy' : (x - 1) * (y - 1) = 6 := by
      have : x * y = 5 + ↑ p := by linarith
      have this' : (x - 1) * (y - 1) = x * y - (x + y) + 1 := by ring
      rw [this',← ht,this] ;simp
    have : ∃ q :ℕ , q = x - 1 := by refine CanLift.prf (x - 1) ?_ ;linarith
    rcases this with ⟨q, hq⟩
    have : q ∣ 2 * 3 := by apply Int.ofNat_dvd.mp ;simp [hq] ;exact Dvd.intro (y - 1) hxy'
    apply Nat.dvd_mul.mp at this
    rcases this with ⟨y',z,hy',hz,hyz⟩
    rcases (Nat.dvd_prime Nat.prime_two).mp hy' with h3|h3
    rcases (Nat.dvd_prime Nat.prime_three).mp hz with h4|h4
    · simp [← hyz,h3,h4] at hq
      simp [← hq] at hxy'
      have hx : x = 2 := by linarith
      have hy : y = 7 := by linarith
      simp [hx,hy] at ht
      have : p = 9 := by exact Int.ofNat_inj.mp ht
      rw [this] at hp ;norm_num at hp
    -- Since $p$ is prime, we get $p=7$.
    · simp [← hyz,h3,h4] at hq
      simp [← hq] at hxy'
      have hx : x = 4 := by linarith
      have hy : y = 3 := by linarith
      simp [hx,hy] at ht
      have : p = 7 := by exact Int.ofNat_inj.mp ht
      simp [this]
    rcases (Nat.dvd_prime Nat.prime_three).mp hz with h4|h4
    -- Since $p$ is prime, we get $p=7$.
    · simp [← hyz,h3,h4] at hq
      simp [← hq] at hxy'
      have hx : x = 3 := by linarith
      have hy : y = 4 := by linarith
      simp [hx,hy] at ht
      have : p = 7 := by exact Int.ofNat_inj.mp ht
      simp [this]
    · simp [← hyz,h3,h4] at hq
      simp [← hq] at hxy'
      have hx : x = 7 := by linarith
      have hy : y = 2 := by linarith
      simp [hx,hy] at ht
      have : p = 9 := by exact Int.ofNat_inj.mp ht
      rw [this] at hp ;norm_num at hp
  rcases (Nat.dvd_prime hp).mp hd2 with h2|h2
  -- Case 1: $x+y=5$ and $x y=2 p$.
  simp [← hd1d2,h1',h2] at ht
  simp [← ht] at hxy
  have : x * y = 2 * ↑ p := by linarith
  -- The equation $x^{2}-5 x+2 p=0$ has at least a solution
  -- so we must have $0 \leq \Delta=25-8 p$ which implies $p \in{2,3}$.
  have h : (0:ℤ) ≤ 25 - 8 * ↑p := by
    have this' : (x + y) ^ 2 - 4 * (x * y) = (x - y) ^ 2 := by ring
    rw [← ht,this] at this'
    have : (5:ℤ) ^ 2 - 4 * (2 * ↑p) = 25 - 8 * ↑p := by ring_nf
    rw [← this,this'] ;exact sq_nonneg (x - y)
  have hp1 : p > 1 := by exact Nat.Prime.one_lt hp
  by_cases h' : p = 2
  · simp [h']
  have hp2 : p > 2 := by exact Nat.lt_of_le_of_ne hp1 fun a ↦ h' (id (Eq.symm a))
  by_cases h'' : p = 3
  · simp [h'']
  have hp3 : p > 3 := by exact Nat.lt_of_le_of_ne hp2 fun a ↦ h'' (id (Eq.symm a))
  have hp4 : 4 ≤ p := by exact hp3
  have hp5 : 8 * 4 ≤ 8 * ↑ p := by exact Nat.mul_le_mul_left 8 hp3
  apply Int.add_le_of_le_sub_right at h ;simp at h
  have hp6 : 8 * p ≤ 25 := by exact Int.ofNat_le.mp h
  have : 8 * 4 ≤ 25 := by linarith
  simp at this
  -- Case 3: $x+y=5 p$ and $x y=p+1$.
  simp [← hd1d2,h1',h2] at ht
  simp [← ht] at hxy ;nth_rewrite 2 [← mul_one ((5:ℤ) * ↑p)] at hxy
  apply mul_left_cancel₀ at hxy
  have this' : x * y = ↑p + 1 := by linarith
  -- We have $(x-1)(y-1)=x y-x-y+1=2-4 p&lt;0$.
  -- But this is impossible since $x, y \geq 1$.
  have hxy'' : (x - 1) * (y - 1) = x * y - (x + y) + 1 := by ring
  rw [this',← ht] at hxy''
  have : (1:ℤ ) ≤ ↑ p := by refine Nat.one_le_cast.mpr ?_ ;exact Nat.Prime.one_le hp
  have : (4:ℤ )*1 ≤ 4 * ↑ p := by refine Int.mul_le_mul_of_nonneg_left this ?_ ;simp
  have : (2:ℤ) < 4 * ↑ p := by linarith
  have h : (x - 1) * (y - 1) < 0 := by rw [hxy''] ;ring_nf ;refine Int.sub_lt_iff.mpr ?_ ;rw [zero_add,mul_comm] ;exact this
  have h' : (x - 1) * (y - 1) ≥ 0 := by refine Int.mul_nonneg ?_ ?_ ;exact Int.sub_nonneg_of_le hx ;exact Int.sub_nonneg_of_le hy
  linarith
  simp ;exact Nat.Prime.ne_zero hp
  -- Finally, the equation has solutions in positive integers only for $p \in{2,3,7}$.
  intro hp
  rcases hp with hp|hp|hp
  · simp [hp] ;use 1 ;simp ;use 4 ;simp
  · simp [hp] ;use 2 ;simp ;use 3 ;simp
  · simp [hp] ;use 3 ;simp ;use 4 ;simp
