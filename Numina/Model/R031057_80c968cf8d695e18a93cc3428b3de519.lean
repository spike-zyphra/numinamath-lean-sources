import Mathlib

  theorem algebra_163002 {b g : ℕ} (hb : b = 314) (hg : g = 322) (hfdj : fdj = (b + g) / 6) (hp : P = (b + g) - fdj):
  fdj = 106 ∧ P = 530:= by
  have h1 : b + g = 636 := by
    calc
      b + g = 314 + 322 := by rw [hb, hg]
      _ = 636 := by norm_num

  have h2 : fdj = 106 := by
    rw [hfdj]
    calc
      (b + g) / 6 = 636 / 6 := by rw [h1]
      _ = 106 := by norm_num

  have h3 : P = 530 := by
    rw [hp]
    calc
      (b + g) - fdj = 636 - 106 := by rw [h1, h2]
      _ = 530 := by norm_num

  constructor
  · exact h2
  · exact h3