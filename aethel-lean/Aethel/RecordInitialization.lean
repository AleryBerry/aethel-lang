import Aethel.LayoutPaths

namespace Aethel.AutomaticLayout

/-- The source supplies one typed value at every integer leaf. Empty records
consume no values. Unused bits, including padding, start at zero. -/
private def initializePaths {abi : TargetIntegerABI} {schema : Schema} {layout : Layout}
    (planned : Conforms abi schema layout) (values : List Nat → Option IntegerBits)
    (image : Image layout.size) : List (List Nat) → Option (Image layout.size)
  | [] => some image
  | path :: rest => do
    let value ← values path
    let next ← writeInteger planned path image value
    initializePaths planned values next rest

def initializeRecord {abi : TargetIntegerABI} {schema : Schema} {layout : Layout}
    (planned : Conforms abi schema layout) (values : List Nat → Option IntegerBits) :
    Option (Image layout.size) :=
  initializePaths planned values (fun _ => 0) layout.leafPaths

private theorem initializePaths_correct {abi : TargetIntegerABI} {schema : Schema} {layout : Layout}
    (planned : Conforms abi schema layout) (values : List Nat → Option IntegerBits)
    {paths : List (List Nat)} {path : List Nat} {image final : Image layout.size}
    (finished : initializePaths planned values image paths = some final)
    (requested : path ∈ paths ∨ readInteger planned path image = values path) :
    readInteger planned path final = values path := by
  induction paths generalizing image with
  | nil =>
    cases finished
    exact requested.resolve_left List.not_mem_nil
  | cons next rest ih =>
    simp only [initializePaths, bind, Option.bind_eq_some_iff] at finished
    obtain ⟨value, supplied, middle, stored, continued⟩ := finished
    apply ih continued
    by_cases same : next = path
    · subst next
      exact .inr ((readInteger_after_write planned path image middle value stored).trans supplied.symm)
    · rcases requested with member | previous
      · exact .inl ((List.mem_cons.mp member).resolve_left (Ne.symm same))
      · exact .inr ((readInteger_preserved_other_path planned same stored).trans previous)

/-- Every resolvable integer leaf is initialized to the supplied value. -/
theorem initialize_correct {abi : TargetIntegerABI} {schema : Schema} {layout : Layout}
    (planned : Conforms abi schema layout) {values : List Nat → Option IntegerBits}
    {image : Image layout.size} {path : List Nat} {field : IntegerField layout.size}
    (initialized : initializeRecord planned values = some image)
    (found : resolveInteger planned path = some field) :
    readInteger planned path image = values path :=
  initializePaths_correct planned values initialized
    (.inl ((resolveInteger_leaf found).mem_leafPaths planned))

theorem initialize_iff_supplied {abi : TargetIntegerABI} {schema : Schema} {layout : Layout}
    (planned : Conforms abi schema layout) (values : List Nat → Option IntegerBits) :
    (∃ image, initializeRecord planned values = some image) ↔
      ∀ path field, resolveInteger planned path = some field →
        ∃ bits : BitVec field.kind.bits, values path = some ⟨field.kind, bits⟩ := by
  constructor
  · rintro ⟨image, initialized⟩ path field found
    exact ⟨field.get image, by simpa [readInteger, found] using
      (initialize_correct planned initialized found).symm⟩
  · intro supplied
    have existsField : ∀ path ∈ layout.leafPaths,
        ∃ field, resolveInteger planned path = some field := by
      intro path member
      obtain ⟨_, _, placement, kind, slot, leaf, _, _⟩ := Layout.leafPaths_sound member
      unfold resolveInteger
      split
      next => exact ⟨_, rfl⟩
      next => simp_all
    have all : ∀ paths : List (List Nat), (∀ path ∈ paths, path ∈ layout.leafPaths) →
        ∀ image, ∃ final, initializePaths planned values image paths = some final := by
      intro paths
      induction paths with
      | nil => intro _ image; exact ⟨image, rfl⟩
      | cons path rest ih =>
        intro included image
        obtain ⟨field, found⟩ := existsField path (included path (by simp))
        obtain ⟨bits, value⟩ := supplied path field found
        obtain ⟨final, doneRest⟩ := ih (fun p member => included p (List.mem_cons_of_mem _ member))
          (field.set image bits)
        exact ⟨final, by simp [initializePaths, value, writeInteger, found, bind, doneRest]⟩
    exact all _ (fun _ member => member) _

end Aethel.AutomaticLayout
