namespace rec CollectionsA

open System.Collections.Generic

module Enumerable =
    
    let enumerator (enumerable: IEnumerable<'T>) = enumerable.GetEnumerator ()