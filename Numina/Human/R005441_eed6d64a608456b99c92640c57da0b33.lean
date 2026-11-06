import Mathlib

-- Define the recurrence sequence for cottage count A : ℕ → ℕ, and the duration per interval (seconds)  interval_duration : ℕ := 480, the goal is to prove that the total number of intervals : num_intervals : ℕ := 4, which means the total_time is 1920 seconds.


-- Define the recurrence sequence for cottage count
def A : ℕ → ℕ
  | 0 => 90        -- Initial number of cottages
  | n+1 => 
      let prev := A n
      if prev = 0 then 0  -- If cottages = 0, remain 0
      else 2 * prev - 96  -- Otherwise apply recurrence relation

-- Prove A 4 = 0
lemma A4_eq_0 : A 4 = 0 := by
  unfold A; unfold A; unfold A; unfold A; rfl

-- Define duration per interval (seconds)
def interval_duration : ℕ := 480

-- Define total number of intervals
def num_intervals : ℕ := 4

-- Define total time (seconds)
def total_time : ℕ := num_intervals * interval_duration

-- Calculate total time = 1920 seconds
example : total_time = 1920 := by
  unfold total_time num_intervals interval_duration
  norm_num

-- At total time (after 4 intervals), cottages = 0 (village burned)
theorem village_burned : A num_intervals = 0 := by
  rw [num_intervals]
  exact A4_eq_0