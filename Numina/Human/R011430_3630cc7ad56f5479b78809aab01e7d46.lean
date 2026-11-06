import Mathlib

/-
Find the primes $p$ such that there exist $x, y \in \mathbb{N}^{*}$ such that

$$
x\left(y^{2}-p\right)+y\left(x^{2}-p\right)=5 p
$$
-/

theorem number_theory_128628 (p : ℕ) (hp : Nat.Prime p) :
(∃ x y : ℕ, (x > 0) ∧ (y > 0) ∧ ((x:ℤ) * (y ^ 2 - p) + y * (x ^ 2 - p) = 5 * p) )
↔
p = 2 ∨ p = 3 ∨ p = 7 := by

  constructor

  --From left to right.
  intro h
  obtain ⟨x,y, xpos, ypos, h⟩ := h

  have xpyg1 : 1 < x + y := by omega
  have pge2 : 2 ≤ p := by exact Nat.Prime.two_le hp

  --Rewrite our equation. We get that x+y ∣ 5*p.
  have eq: (x+y) * (x*y - p) = 5 * p := by
    have : (x:ℤ) * ((y:ℤ)^ 2 - p) + (y:ℤ) * ((x:ℤ)^2 - ↑p) = ((x:ℤ)+y)*(x*y-p) := by ring
    rw [this] at h
    have : 0 < @HSub.hSub ℤ ℤ ℤ instHSub (↑x * ↑y) ↑p := by
      have : 0< @HAdd.hAdd ℤ ℤ ℤ instHAdd ↑x ↑y := by norm_cast; linarith only [xpos, ypos]
      have : 0 < @HMul.hMul ℤ ℤ ℤ instHMul 5 ↑p := by norm_cast; linarith only [pge2]
      nlinarith
    zify
    have : @Nat.cast ℤ AddMonoidWithOne.toNatCast (x * y - p) = @HSub.hSub ℤ ℤ ℤ instHSub (↑x * ↑y) ↑p := by
      omega
    rw [this]
    exact h
  have dd: (x+y) ∣ 5*p := by use (x*y-p); omega

  --Hence, x+y = 1 or 5 or p or 5*p. We just need to check every case separately.
  by_cases xy5 : x+y = 5
  rw [xy5] at eq
  field_simp at eq
  have dxy : x*y = 2 * p := by omega
  have dx : x ∣ 2*p := by use y;omega
  by_cases d2x : 2 ∣ x
  obtain ⟨l,hl⟩ := d2x
  obtain ⟨k,hk⟩ := dx
  have ldp: l ∣ p := by 
    use k
    simp [hl] at hk;
    linarith
  rw [Nat.dvd_prime] at ldp
  rcases ldp with ldp | ldp
  have xe : x = 2 := by omega
  have ye : y = 3 := by omega
  have : p = 3 := by rw [xe,ye] at dxy; linarith
  right; left;exact this
  have ye : y = 1 := by omega
  have xe : x = 4 := by rw [ye] at xy5; linarith
  have pe : p = 2 := by rw [ye,xe] at dxy; linarith
  left; exact pe
  exact hp
  have : Nat.Coprime x 2 := by 
    rw [Nat.Prime.dvd_iff_not_coprime] at d2x
    push_neg at d2x
    exact Nat.coprime_comm.mp d2x
    norm_num

  have : x ∣ p := by exact Nat.Coprime.dvd_of_dvd_mul_left this dx
  rw [Nat.dvd_prime] at this
  rcases this with xe | xe
  have ye : y = 4 := by rw [xe] at xy5; linarith
  have pe : p = 2 := by rw [xe,ye] at dxy; linarith
  left; exact pe
  have ye : y = 2 := by rw [xe] at dxy; omega
  have xe : x = 3 := by rw [ye] at xy5; linarith
  have pe : p = 3 := by rw [xe,ye] at dxy; linarith
  right;left; exact pe
  exact hp

  by_cases xyp : x+y = p
  rw [xyp] at eq
  have t1: x*y = p + 5 := by nlinarith
  have xypro: (x-1)*(y-1) = 6 := by
    zify at xyp t1 ⊢
    field_simp
    linarith
  have dx: x-1 ∣ 6 := by use y-1; symm; exact xypro
  have : Nat.divisors 6 = {1,2,3,6} := by decide
  have hdx : (x-1) ∈ Nat.divisors 6 := by refine Nat.mem_divisors.mpr ?_; simp [dx]
  rw [this] at hdx;
  simp at hdx
  rcases hdx with hx | hx | hx | hx
  have ye: y = 7 := by simp [hx] at xypro; exact xypro
  have pe : p = 9 := by rw [hx,ye] at t1; simp at t1; exact t1
  exfalso;
  rw [pe] at hp; norm_num at hp
  have ye: y = 4 := by simp [hx] at xypro; omega
  simp [hx,ye] at xyp
  right;right; symm; exact xyp
  have ye: y = 3 := by simp [hx] at xypro; omega
  simp [hx,ye] at xyp
  right;right; symm; exact xyp
  have ye: y = 2 := by simp [hx] at xypro; omega
  simp [hx,ye] at xyp
  rw [←xyp] at hp; norm_num at hp

  by_cases xy5p : x+y = 5*p
  simp [xy5p] at eq
  have t1: x*y = p + 1 := by
    zify at eq xy5p ⊢;
    nlinarith
  have : ((x:ℤ)-1)*(y-1) = 2 - 4 * p := by nlinarith
  have : 2 - 4 * p < 0:= by nlinarith
  have : 0 ≤ ((x:ℤ)-1)*(y-1) := by norm_cast
  linarith

  by_cases d5xy : 5 ∣ x + y
  obtain ⟨l,hl⟩ := d5xy
  obtain ⟨k,hk⟩ := dd
  have ldp : l ∣ p := by use k; rw [hl] at hk; linarith
  rw [Nat.dvd_prime] at ldp
  rcases ldp with ldp | ldp
  have : x + y = 5 := by rw [ldp] at hl; norm_num at hl; exact hl
  contradiction
  have : x + y = 5*p:= by rw [ldp] at hl; exact hl
  contradiction
  exact hp
  have : Nat.Coprime (x+y) 5 := by 
    rw [Nat.Prime.dvd_iff_not_coprime] at d5xy;  
    push_neg at d5xy
    exact Nat.coprime_comm.mp d5xy
    norm_num
  have xydp : x+y ∣ p := by exact Nat.Coprime.dvd_of_dvd_mul_left this dd
  rw [Nat.dvd_prime] at xydp
  rcases xydp with xydp | xydp
  linarith
  contradiction
  exact hp


  --From right to left. Simple verification.
  intro h
  rcases h with h | h | h

  use 1,4
  rw [h]
  field_simp
  norm_num


  use 3,2
  simp [h]

  use 3,4
  simp [h]
