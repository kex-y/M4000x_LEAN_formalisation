/- Formalisation of Groups from the module Linear Algebra and Groups -/
import tactic
/- Chapter 1. Groups and Subgroups -/

namespace M40004

-- Definition of a group
@[simp] def is_assoc (G : Type*) (operat : G → G → G) := 
∀ g h k : G, operat (operat g h) k = operat g (operat h k)

@[simp] def is_identity (G : Type*) (operat : G → G → G) (e : G) :=
∀ g : G, operat g e = operat e g ∧ operat g e = g

@[simp] def has_identity (G : Type*) (operat : G → G → G) :=
∃ e : G, is_identity G operat e

@[simp] def is_inverse (G : Type*) (operat : G → G → G) (g h : G) :=
operat g h = operat h g ∧ is_identity G operat (operat g h)

@[simp] def has_inverse (G : Type*) (operat : G → G → G) :=
∀ g : G, ∃ h : G, is_inverse G operat g h

structure is_group (G : Type*) (operat : G → G → G) :=
(group_assoc : is_assoc G operat)
(group_identity : has_identity G operat)
(group_inverse : has_inverse G operat)

-- A group has a unique identity
theorem unique_identity {G : Type*} {operat : G → G → G} :
∀ e₁ e₂ : G, is_identity G operat e₁ ∧ is_identity G operat e₂ →  e₁ = e₂ :=
begin
    rintros e₁ e₂ ⟨id₁, id₂⟩,
    rw [←(id₂ e₁).right, (id₂ e₁).left],
    from (id₁ e₂).right
end

-- An element in a group has an unique inverse
theorem unique_inverse {G : Type*} {operat : G → G → G} (hgp : is_group G operat) :
∀ g h k : G, is_inverse G operat g h ∧ is_inverse G operat g k → h = k :=
begin
    rintros g h k ⟨invh, invk⟩,
    have : operat (operat k g) h = h :=
        by {cases invk with heq hid,by 
            rw [←heq, ←(hid h).left, (hid h).right]
        },
    rw [←this, hgp.group_assoc],
    repeat {swap, assumption},
    suffices : is_identity G operat (operat g h),
        rwa (this k).right,
    from invh.right
end

-- Some lemmas that makes working easier
lemma operat_both_sides {G : Type*} {operat : G → G → G} {hgp : is_group G operat} (a b c : G) :
b = c → operat a b = operat a c := λ h, by {rw h}

-- Some properties of a group

-- If ab = ac then b = c
theorem left_operat_cancel {G : Type*} {operat : G → G → G} (hgp : is_group G operat) :
∀ a b c : G, operat a b = operat a c → b = c :=
begin
    intros a b c h,
    cases hgp.group_inverse a with ainv hainv,
    suffices : operat ainv (operat a b) = operat ainv (operat a c),
        repeat {rw ←hgp.group_assoc at this},
        sorry,
    sorry
end

end M40004
