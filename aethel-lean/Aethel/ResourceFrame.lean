import Aethel.ResourceLiveness

namespace Aethel.Core

theorem State.store_byte_other (s : State) (written observed : ByteLocation) (value : UInt8)
    (different : written ≠ observed) :
    (s.store written value).byte observed = s.byte observed := by
  simp only [State.byte, State.allocation, State.store, List.find?_map, Function.comp_def]
  generalize h : s.allocations.find? (fun a => a.owner == observed.allocation) = found
  cases found <;> simp only [Option.map_none, Option.map_some, bind, Option.bind]
  rename_i allocation
  have owner : allocation.owner = observed.allocation := by simpa using List.find?_some h
  by_cases same : observed.allocation = written.allocation <;>
    simp [owner, same, List.getElem?_set]
  exact fun equalOffset => False.elim (different (by cases written; cases observed; congr; exact same.symm))

theorem State.store_byte_written (s : State) (p : ByteLocation) (old value : UInt8)
    (live : s.byte p = some old) :
    (s.store p value).byte p = some value := by
  simp only [State.byte, State.allocation, State.store, List.find?_map, Function.comp_def]
  simp only [State.byte, State.allocation, bind, Option.bind_eq_some_iff] at live
  obtain ⟨allocation, found, read⟩ := live
  have owner : allocation.owner = p.allocation := by simpa using List.find?_some found
  have bound := (List.getElem?_eq_some_iff.mp read).choose
  simp [found, owner, bind, bound]

theorem Step.write_frame {s next : State} {id : HandleId} {h : Handle} {value : UInt8}
    (step : Step s (.write id value) next) (found : s.handle id = some h)
    (observed : ByteLocation) (different : h.location ≠ observed) :
    next.byte observed = s.byte observed := by
  cases step
  rename_i writer old authority alive available lookup
  have same := Option.some.inj (lookup.symm.trans found)
  exact s.store_byte_other writer.location observed value (same.symm ▸ different)

end Aethel.Core
