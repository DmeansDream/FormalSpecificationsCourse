module SharedClasse
{
    class NPC
    {
        const name : string
        const age : string
        const faction : string

        constructor(n : string, a : string, f : string)
            ensures name == n
            ensures age == a
            ensures faction == f
        {
            name := n;
            age := a;
            faction := f;
        }
    }
}

module Flyweight
{
    import opened SharedClasse

    class NPCRegistry
    {
        var cache : map<string, NPC>

        constructor()
        {
            cache := map[];
        }

        method GetNPC(n : string, a : string, f : string) returns (npc : NPC)
            modifies this
            ensures n in old(cache) ==> npc == old(cache[n]) && cache == old(cache)
            ensures n !in old(cache) ==> fresh(npc) && cache == old(cache)[n := npc] && npc == cache[n]
        {
            if n in cache
            {
                npc := cache[n];
                return npc;
            }
            else
            {
                npc := new NPC(n,a,f);
                cache := cache[n := npc];
                return npc;
            }
        } 
    }
}

module Singleton
{
    import opened SharedClasse

    class NPCSingleton
    {
        var instance : NPC?

        constructor()
            ensures instance == null
        {
            instance := null;
        }

        method GetNPC(n : string, a : string, f : string) returns (npc : NPC)
            modifies this
            ensures instance == npc
            ensures old(instance) == null ==> fresh(instance)
            ensures old(instance) != null ==> instance == old(instance)
        {
            if instance == null
            {
                npc := new NPC(n,a,f);
                instance := npc;
                return instance;
            }
            else
            {
                return instance;
            }
            
        } 
    }
}

method Main()
{
    var registry := new Flyweight.NPCRegistry();

    var npc1 := registry.GetNPC("Bob Boblehead", "20", "Gang");
    var npc2 := registry.GetNPC("Bob Boblehead", "20", "Gang");

    assert npc1 == npc2;

    var singleton := new Singleton.NPCSingleton();

    var npc3 := singleton.GetNPC("Dallas", "46", "Gang");
    var npc4 := singleton.GetNPC("Dallas", "46", "Gang");

    assert npc3 == npc4;
}