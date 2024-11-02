/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 6 : "or" (∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases'` (new functionality)

-/


-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.
variable (P Q R S : Prop)

example : P → P ∨ Q := by
  intro h1
  left
  assumption
  done

example : Q → P ∨ Q := by
  intro h1
  right
  assumption
  done

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro h1
  intro h2
  intro h3
  cases' h1 with hP hQ
  apply h2 at hP
  exact hP
  apply h3 at hQ
  exact hQ
  done

-- symmetry of `or`
example : P ∨ Q → Q ∨ P := by
  intro h
  cases' h with hP hQ
  right
  assumption
  left
  assumption
  done

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
  intro h
  cases' h with hPQ hR
  cases' hPQ with hP hQ
  left
  assumption
  right
  left
  assumption
  right
  right
  assumption
  intro h
  cases' h with hP hQR
  left
  left
  assumption
  cases' hQR with hQ hR
  left
  right
  assumption
  right
  assumption
  done

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  intro h1
  intro h2
  intro h3
  cases' h3 with hP hQ
  apply h1 at hP
  left
  assumption
  apply h2 at hQ
  right
  assumption
  done

example : (P → Q) → P ∨ R → Q ∨ R := by
  intro h1
  intro h2
  cases' h2 with hP hR
  left
  apply h1 at hP
  assumption
  right
  assumption
  done

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  intro h1
  intro h2
  rw [h1, h2]
  done

-- de Morgan's laws
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  intro h
  change (P ∨ Q) → False at h
  constructor
  change P → False
  intro hP
  apply h
  left
  assumption
  change Q → False
  intro hQ
  apply h
  right
  assumption
  intro h
  cases' h with hnP hnQ
  change P → False at hnP
  change Q → False at hnQ
  change P ∨ Q → False
  intro h
  cases' h with hP hQ
  apply hnP
  assumption
  apply hnQ
  assumption
  done

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  intro h1
  by_cases hP: P
  change (P ∧ Q) → False at h1
  right
  change Q → False
  intro hQ
  apply h1
  constructor
  assumption
  assumption
  left
  assumption
  intro h
  change (P ∧ Q) → False
  intro hPQ
  cases' hPQ with hP hQ
  cases' h with hnP hnQ
  change P → False at hnP
  apply hnP
  assumption
  change Q → False at hnQ
  apply hnQ
  assumption
  done
