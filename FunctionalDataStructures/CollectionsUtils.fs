namespace rec CollectionsA

open System.Collections.Generic

module Enumerable =
    
    let inline enumerator (enumerable: IEnumerable<'T>) = enumerable.GetEnumerator ()