using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace CSharpRewrite
{
    public enum State
    {
        Boot,
        Closed,
        Open,
        Processing
    }

    public sealed class Turnstile : IBaseValidation
    {
        public const int TickCount = 1000;
        public const int PersonTick = 200;

        public State state { get; private set; }
        public bool gate { get; private set; }
        public double bill { get; }

        public int timerTicks { get; private set; }
        public bool personPassed { get; private set; }

        public Turnstile(State state, double payment)
        {
            if (state != State.Boot) throw new InvalidOperationException("Initial state must be Boot");

            if (payment <= 0.0) throw new InvalidOperationException("Payment must be > 0");

            this.state = state;
            bill = payment;

            gate = false;
            timerTicks = 0;
            personPassed = false;

            if (!Valid()) throw new InvalidOperationException("Valid() failed");
        }

        public bool Valid()
        {
            if (bill <= 0.0) return false;

            if (state == State.Open)
            {
                if (!gate) return false;
                if (timerTicks <= 0 && !personPassed) return false;
            }

            if (state == State.Closed && gate) return false;
            if (state == State.Boot && gate) return false;
            if (state == State.Processing && gate) return false;

            if ((state == State.Closed || state == State.Boot || state == State.Processing)
                && timerTicks != 0)
                return false;

            return true;
        }

        public void Initialize()
        {
            if (!Valid()) throw new InvalidOperationException("Valid() failed");
            if (state != State.Boot) throw new InvalidOperationException("State must be Boot");

            state = State.Closed;
            gate = false;
            timerTicks = 0;
            personPassed = false;

            if (!Valid()) throw new InvalidOperationException("Valid() failed");
        }

        public bool ProcessNFCSource(INFCSource source)
        {
            if (!Valid()) throw new InvalidOperationException("Valid() failed");
            if (source == null) throw new InvalidOperationException("source is null");
            if (!source.Valid()) throw new InvalidOperationException("source invalid");
            if (state != State.Closed) throw new InvalidOperationException("State must be Closed");

            if (source is RiderPass pass)
                return ProcessRiderPass(pass);

            if (source is PaymentCard card)
                return ProcessPaymentCard(card);

            return false;
        }

        private bool ProcessRiderPass(RiderPass pass)
        {
            state = State.Processing;

            long id = pass.Read();

            if (id < 0 || !HasKDigits(id, 8))
            {
                state = State.Closed;
                Console.WriteLine("Error in ID");
                return false;
            }

            if (pass.GetRides() <= 0)
            {
                state = State.Closed;
                Console.WriteLine("Low on rides");
                return false;
            }

            pass.ConsumeRide();
            state = State.Closed;
            DoorCycle(TickCount, PersonTick);
            return true;
        }

        private bool ProcessPaymentCard(PaymentCard card)
        {
            state = State.Processing;

            long id = card.Read();

            if (id < 0 || !HasKDigits(id, 16))
            {
                state = State.Closed;
                Console.WriteLine("Error in ID");
                return false;
            }

            if (!LuhnValid(id))
            {
                state = State.Closed;
                Console.WriteLine("Failed Luhn check");
                return false;
            }

            if (card.GetBal() <= 0.0 || card.GetBal() < bill)
            {
                state = State.Closed;
                Console.WriteLine("Low balance");
                return false;
            }

            card.Deduct(bill);
            state = State.Closed;
            DoorCycle(TickCount, PersonTick);
            return true;
        }

        public void DoorCycle(int ticks, int personAtTick)
        {
            if (!Valid()) throw new InvalidOperationException("Valid() failed");
            if (state != State.Closed) throw new InvalidOperationException("State must be Closed");
            if (personAtTick < 0 || personAtTick >= ticks) throw new InvalidOperationException("Invalid person tick");

            OpenTurner(ticks);

            int i = 0;
            while (i < ticks && state == State.Open)
            {
                if (i == personAtTick && personAtTick > 0)
                    PersonPassedEvent();
                else
                    Tick();
                i++;
            }
            Console.WriteLine($"Turner closed at: {i - 1}");
        }

        public void OpenTurner(int ticks)
        {
            if (!Valid()) throw new InvalidOperationException("Valid() failed");
            if (ticks <= 0) throw new InvalidOperationException("ticks must be > 0");
            if (state != State.Closed) throw new InvalidOperationException("State must be Closed");

            state = State.Open;
            gate = true;
            timerTicks = ticks;
            personPassed = false;

            Console.WriteLine("Turner opened");
        }

        public void PersonPassedEvent()
        {
            if (!Valid()) throw new InvalidOperationException("Valid() failed");
            if (state != State.Open) throw new InvalidOperationException("State must be Open");

            state = State.Closed;
            gate = false;
            timerTicks = 0;
            personPassed = true;

            Console.WriteLine("Person passed");
        }

        public void Tick()
        {
            if (!Valid()) throw new InvalidOperationException("Valid() failed");
            if (state != State.Open) throw new InvalidOperationException("State must be Open");

            timerTicks--;

            if (timerTicks == 0)
            {
                state = State.Closed;
                gate = false;
            }
        }

        public static bool LuhnValid(long id)
        {
            if (id < 0) return false;
            if (!HasKDigits(id, 16)) return false;

            int[] digits = ExtractDigits(id);
            return LuhnSum(digits, digits.Length, false) % 10 == 0;
        }

        private static int LuhnSum(int[] digits, int i, bool even)
        {
            if (i == 0) return 0;

            int d = digits[i - 1];
            int doubled = even ? (d * 2 > 9 ? d * 2 - 9 : d * 2) : d;

            return doubled + LuhnSum(digits, i - 1, !even);
        }

        private static int[] ExtractDigits(long n)
        {
            if (n == 0) return new[] { 0 };

            string s = n.ToString();
            int[] result = new int[s.Length];

            for (int i = 0; i < s.Length; i++)
                result[i] = s[i] - '0';

            return result;
        }

        public static bool HasKDigits(long n, int k)
        {
            if (k < 1) throw new InvalidOperationException("k must be >= 1");
            if (n < 0) return false;

            long lower = Pow10(k - 1);
            long upper = Pow10(k);

            return lower <= n && n < upper;
        }

        public static long Pow10(int exp)
        {
            if (exp < 0) throw new InvalidOperationException("exp must be >= 0");
            if (exp == 0) return 1;

            return 10 * Pow10(exp - 1);
        }
    }
}
