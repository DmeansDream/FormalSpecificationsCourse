using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Security.Cryptography;
using System.Text;
using System.Threading.Tasks;

namespace CSharpRewrite
{
    public interface IBaseValidation
    {
        bool Valid();
    }

    public interface INFCSource : IBaseValidation
    {
        long Read();
    }

    public interface IPass : IBaseValidation
    {
        int rides { get; }
        int GetRides();
        void ConsumeRide();
    }

    public interface IDeductable : IBaseValidation
    {
        double balance { get; }
        double GetBal();
        void Deduct(double bill);
    }
    public sealed class RiderPass : INFCSource, IPass
    {
        public long ID { get; }

        public int rides { get; private set; }

        public RiderPass(long id, int rides)
        {
            if (rides < 0) throw new InvalidOperationException("rides precondition failed");

            ID = id;
            this.rides = rides;

            if (!Valid()) throw new InvalidOperationException("Valid() failed");
        }

        public bool Valid()
        {
            return rides >= 0;
        }

        public long Read()
        {
            if (!Valid()) throw new InvalidOperationException("Valid() failed");
            return ID;
        }

        public int GetRides()
        {
            if (!Valid()) throw new InvalidOperationException("Valid() failed");
            return rides;
        }

        public void ConsumeRide()
        {
            if (!Valid()) throw new InvalidOperationException("Valid() failed");
            if (rides <= 0) throw new InvalidOperationException("rides precondition failed");

            int oldRides = rides;

            rides--;

            if (!Valid()) throw new InvalidOperationException("Valid() failed");
            if (rides != oldRides - 1) throw new InvalidOperationException("rides decrement failed");
        }
    }

    public class PaymentCard : INFCSource, IDeductable
    {
        public long ID { get; }

        public double balance { get; private set; }

        public PaymentCard(long id, double balance)
        {
            if (balance < 0.0) throw new InvalidOperationException("balance >= 0 failed");

            ID = id;
            this.balance = balance;

            if (!Valid()) throw new InvalidOperationException("Valid() failed");
            if (this.balance != balance) throw new InvalidOperationException("balance init failed");
            if (ID != id) throw new InvalidOperationException("ID init failed");
        }

        public bool Valid()
        {
            return balance >= 0.0;
        }

        public long Read()
        {
            if (!Valid()) throw new InvalidOperationException("Valid() failed");
            return ID;
        }

        public double GetBal()
        {
            if (!Valid()) throw new InvalidOperationException("Valid() failed");
            return balance;
        }

        public void Deduct(double bill)
        {
            if (!Valid()) throw new InvalidOperationException("Valid() failed");
            if (bill < 0.0) throw new InvalidOperationException("bill > 0 failed");
            if (bill > GetBal()) throw new InvalidOperationException("bill <= balance failed");

            double oldBalance = balance;

            balance -= bill;

            if (!Valid()) throw new InvalidOperationException("Valid() failed");
            if (balance != oldBalance - bill) throw new InvalidOperationException("balance deduct failed");
        }
    }
}
