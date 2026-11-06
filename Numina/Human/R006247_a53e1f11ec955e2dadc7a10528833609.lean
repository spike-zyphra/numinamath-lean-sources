import Mathlib

lemma I_dvd_mul_right_of_dvd {a b : Nat} (h : a ∣ b) (c : Nat) : a ∣ b * c :=
  Nat.dvd_trans h (Nat.dvd_mul_right _ _)

/- use to show gcd(d, a) = gcd(d,b) = 1. -/
lemma lemma_1
  (a b u v : ℕ)
  (ab : a.gcd b = 1)
  (av : a.gcd v = 1)
  : let d := (a*b).gcd (a*u + b*v);
    d.gcd a = 1 :=
by
  intro d
  let g := d.gcd a
  have : g ∣ a*u + b*v := by
    trans d
    . simp[g]
      exact Nat.gcd_dvd_left d a
    . simp[d]
      exact Nat.gcd_dvd_right (a * b) (a * u + b * v)
  have : g ∣ a * u := by
    apply I_dvd_mul_right_of_dvd
    simp [g]
    exact Nat.gcd_dvd_right d a
  have : g ∣ b*v := by
    apply (Nat.dvd_add_iff_right this).mpr
    assumption
  have : g.gcd b = 1 := by
    exact Nat.Coprime.gcd_left d ab
  have : g ∣ v := by
    apply Nat.Coprime.dvd_of_dvd_mul_left this
    assumption
  have : g ∣ a.gcd v := by
    have : g ∣ a := by simp[g]; exact Nat.gcd_dvd_right d a
    apply Nat.dvd_gcd
    <;> assumption
  simp [av, g] at this
  assumption

/- Theorem: Let $a, b, x, y$ be integers. If $a$ and $b$ are coprime, $a$ and $y$ are coprime, and $b$ and $x$ are coprime, then $ab$ and $xa+yb$ are coprime. -/
theorem number_theory_635135
    (a b x y : ℕ)
    (hcoprime : a.Coprime b ∧ a.Coprime y ∧ b.Coprime x)
    : (a * b).Coprime (x * a + y * b) :=
by
  generalize dh : (a * b).gcd (x * a + y * b) = d
  -- Two step are same.
  have h1 := lemma_1 a b x y (by tauto) (by tauto)
  have h2 := lemma_1 b a y x (by rw [Nat.gcd_comm]; tauto) (by tauto)

  simp at h1 h2
  rw [mul_comm a x, mul_comm b y, dh] at h1
  rw [mul_comm, add_comm, mul_comm b y, mul_comm a x, dh] at h2
  have : d.gcd (a*b) = 1 := Nat.Coprime.mul_right h1 h2
  have : d.gcd (a*b) = d := by
    rw [←dh]
    exact Nat.gcd_gcd_self_left_left (a * b) (x * a + y * b)
  have : d = 1 := by
    rw [←this]
    assumption
  rw [←dh] at this
  assumption
