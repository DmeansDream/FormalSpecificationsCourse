using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace CSharpRewrite
{
    internal class Program
    {
        static void Main(string[] args)
        {
            var turnstile = new Turnstile(State.Boot, 20.0);
            var pass = new RiderPass(88884444, 2);
            var card = new PaymentCard(4444333322221111, 50.0);
            var falseCard = new PaymentCard(5089689782389771, 50.0);

            turnstile.Initialize();

            Console.WriteLine($"# False Card Test#");
            bool test = turnstile.ProcessNFCSource(falseCard);

            Console.WriteLine($"Operation completed?: {test}");
            Debug.Assert(test == false);

            Console.WriteLine($"# Working Pass Test#");
            Console.WriteLine($"# Rides : {pass.rides} #");
            bool res1 = turnstile.ProcessNFCSource(pass);
            Console.WriteLine($"Operation completed?: {res1}");
            Console.WriteLine($"# Rides : {pass.rides} #");
            Debug.Assert(pass.rides == 1);
            
            bool res2 = turnstile.ProcessNFCSource(pass);
            Console.WriteLine($"Operation completed?: {res2}");
            Console.WriteLine($"# Rides : {pass.rides} #");
            Debug.Assert(pass.rides == 0);

            bool res3 = turnstile.ProcessNFCSource(pass);
            Console.WriteLine($"Operation completed?: {res3}");
            Console.WriteLine($"# Rides : {pass.rides} #");
            Debug.Assert(!res3);

            Console.WriteLine($"# Working Card Test#");
            Console.WriteLine($"# Balance : {card.balance} #");
            bool res4 = turnstile.ProcessNFCSource(card);
            Console.WriteLine($"Operation completed?: {res4}");
            Console.WriteLine($"# Balance  : {card.balance} #");
            Debug.Assert(card.balance == 30.0);

            bool res5 = turnstile.ProcessNFCSource(card);
            Console.WriteLine($"Operation completed?: {res5}");
            Console.WriteLine($"# Balance  : {card.balance} #");
            Debug.Assert(card.balance == 10.0);

            bool res6 = turnstile.ProcessNFCSource(card);
            Console.WriteLine($"Operation completed?: {res6}");
            Console.WriteLine($"# Balance  : {card.balance} #");
            Debug.Assert(card.balance == 10.0);
        }
    }
}
