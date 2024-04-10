/**
* basic encrypted messaging program
* Author: Kilian Jakstis
*/

using System.Security.Cryptography;
using System.Numerics;
using System.Text;
using System.Text.Json;
using System.Text.Json.Serialization;

namespace MessengerConsoleApp {

/**
* Key generation, encryption, decryption, etc functions
*/
public static class NumberFunctions {

    // lock for ensuring mutual exclusion of variables used to generate primes
    private static readonly object LockPrime = new();

    /**
    * Helper method for decomposing odd number into 2^r * d + 1
    * param: BigInt i - number to decompose
    * return: int r, int d - respective values
    */
    private static (BigInteger r, BigInteger d) Decomposition(BigInteger i) {
        i -= 1;
        BigInteger r = 0;
        while (i % 2 == 0){
            i /= 2;
            r++;
        }
        return (r, i);
    }

    /**
    * Miller-Rabin primality test method
    * param: BigInt value - the number to test primality
    * param: int k - number of trials
    * return: true if prime else false
    */
    private static bool IsProbablyPrime(this BigInteger value, int k = 10) {
        RandomNumberGenerator rng = RandomNumberGenerator.Create();
        byte[] random_bytes = new byte[value.ToByteArray().Length];
        var (r, d) = Decomposition(value);
        foreach (var _ in Enumerable.Range(0, k)) {
            rng.GetBytes(random_bytes);
            BigInteger candidate_factor = new BigInteger(random_bytes) % (value - 2) + 2;
            var x = BigInteger.ModPow(candidate_factor, d, value);
            if (x == 1 || x == value - 1) {
                continue;
            }
            for (BigInteger l = 0; l < r - 1; l++){
                x = BigInteger.ModPow(x, 2, value);
                if (x == 1) {
                    return false;
                }
                if (x == value - 1) {
                    break;
                }
            }
            if (x != value - 1){
                return false;
            }
        }
        return true;
    }

    /**
    * Generate random BigInt of specified length
    * param: int length - bit length of int to generate
    * return: random BigInt
    */
    private static BigInteger GenerateOddInt(int length){
        RandomNumberGenerator rng = RandomNumberGenerator.Create();
        byte[] random_bytes = new byte[length / 8];
        rng.GetBytes(random_bytes);
        BigInteger i = new(random_bytes);
        // if negative, multiply by -1
        if (i < 0){
            i *= -1;
        }
        // if even, add 1
        if (i % 2 == 0){
            return i + 1;
        } 
        return i;
    }

    /**
    * Generate a prime BigInt in parallel
    * param: int length - bit length of number to generate
    * return: prime BigInt
    */
    private static BigInteger ParallelGetPrime(int length) {
        BigInteger prime = 0;
        bool primeGenerated = false;
        // thread pool all try to generate a prime until one finally does
        Parallel.For (0, int.MaxValue, (index, state) => {
            while(!primeGenerated) {
                BigInteger candidate = GenerateOddInt(length);
                if (candidate.IsProbablyPrime()) {
                    lock (LockPrime) {
                        prime = candidate;
                        primeGenerated = true;
                        state.Break();
                    }
                }
            }
        });
        return prime;
    }

    /**
    * Mod inverse function
    */
    static BigInteger ModInverse(BigInteger a, BigInteger b) {
        BigInteger i = b, v = 0, d = 1; 
        while (a>0) {
            BigInteger z = i/a, x = a; 
            a = i % x;
            i = x;
            x = d;
            d = v - z*x;
            v = x;
        }
        v %= b;
        if (v<0) v = (v+b) % b; 
        return v;
    }

    /**
    * Get private key from RSA alg
    */
    private static BigInteger GetPrivateKey(BigInteger public_key, BigInteger totient) {
        BigInteger a = ModInverse(public_key, totient);
        BigInteger d = BigInteger.ModPow(a, 1, totient);
        d = d < 0 ? d + totient : d;
        return d;
    }

    /**
    * Get public key from RSA alg
    */
    private static BigInteger GetPublicKey(int length, BigInteger totient) {
        BigInteger i = ParallelGetPrime(length);
        while (BigInteger.ModPow(i, 1, totient) == 0 || i >= totient) {
            i = ParallelGetPrime(length);
        }
        return i;
    }

    /**
    * Generate public, private, and N values from RSA alg
    */
    public static (BigInteger, BigInteger, BigInteger) GenerateKeys(int bit_length) {
        int p_length = (int)((bit_length / 2) - (bit_length * 0.2));
        BigInteger p = ParallelGetPrime(p_length);
        BigInteger q = ParallelGetPrime(bit_length - p_length);
        BigInteger n = p * q;
        BigInteger totient = (p - 1) * (q - 1);
        BigInteger e = GetPublicKey(p_length, totient);
        BigInteger d = GetPrivateKey(e, totient);
        return (e, d, n);
    }

    /**
    * Convert BigInt keys to Base64 strings
    */
    public static (string, string) FormatKeys(BigInteger e, BigInteger d, BigInteger n) {
        // n
        byte[] n_bytes = n.ToByteArray();
        byte[] n_length_bytes = BitConverter.GetBytes(n_bytes.Length);
        Array.Reverse(n_length_bytes);
        // e
        byte[] e_bytes = e.ToByteArray();
        byte[] e_length_bytes = BitConverter.GetBytes(e_bytes.Length);
        Array.Reverse(e_length_bytes);
        byte[] e_all_key_bytes = e_length_bytes.Concat(e_bytes).Concat(n_length_bytes).Concat(n_bytes).ToArray();
        string e_format = Convert.ToBase64String(e_all_key_bytes);
        // d
        byte[] d_bytes = d.ToByteArray();
        byte[] d_length_bytes = BitConverter.GetBytes(d_bytes.Length);
        Array.Reverse(d_length_bytes);
        byte[] d_all_key_bytes = d_length_bytes.Concat(d_bytes).Concat(n_length_bytes).Concat(n_bytes).ToArray();
        string d_format = Convert.ToBase64String(d_all_key_bytes);
        return (e_format, d_format);
    }

    /**
    * Derive key value and totient value from Base64 encoded string
    */
    public static (BigInteger, BigInteger) DeriveKey(string s) {
        // all bytes
        byte[] all_bytes = Convert.FromBase64String(s);
        // get key length
        byte[] key_length_bytes = new byte[4];
        Array.Copy(all_bytes, 0, key_length_bytes, 0, 4);
        Array.Reverse(key_length_bytes);
        int key_length =BitConverter.ToInt32(key_length_bytes, 0);
        // get key value
        byte[] key_bytes = new byte[key_length];
        Array.Copy(all_bytes, 4, key_bytes, 0, key_length);
        BigInteger key = new(key_bytes);
        // get totient
        byte[] totient_bytes = new byte[all_bytes.Length - 8 - key_length];
        Array.Copy(all_bytes, 8 + key_length, totient_bytes, 0, all_bytes.Length - 8 - key_length);
        BigInteger totient = new(totient_bytes);
        return (key, totient);
    }

    // decrypt message
    public static string Decrypt(BigInteger d, BigInteger n, string s) {
        byte[] cypher_text_bytes = Convert.FromBase64String(s);
        byte[] decrypted_bytes = RSA_Routine(cypher_text_bytes, d, n);
        string msg = Encoding.UTF8.GetString(decrypted_bytes);
        return msg;
    }

    // convert byte array representing text to BigInt and raise to key power and mod by totient - return mutated bytes
    private static byte[] RSA_Routine(byte[] data, BigInteger x, BigInteger n) {
        BigInteger data_int = new(data);
        BigInteger encrypted_int = BigInteger.ModPow(data_int, x, n);
        byte[] encrypted_bytes = encrypted_int.ToByteArray();
        return encrypted_bytes;
    }

    // encrypt message
    public static string Encrypt(BigInteger e, BigInteger n, string s) {
        byte[] messageBytes = Encoding.UTF8.GetBytes(s);
        byte[] encrypted_bytes = RSA_Routine(messageBytes, e, n);
        string encrypted_string = Convert.ToBase64String(encrypted_bytes);
        return encrypted_string;
    }
}

/**
* Class for representing public key - 1 email
*/
public class PublicKey {

    [JsonPropertyName("email")]
    public string? Email {get; set;}

    [JsonPropertyName("key")]
    public string? Key {get; set;}

    // empty constructor bc of some JsonSerializer warning
    public PublicKey(){}

    public PublicKey(string? email, string key) {
        Email = email;
        Key = key;
    }
}

/**
* Class for representing private keys - list of emails
*/
public class PrivateKey {

    [JsonPropertyName("email")]
    public string[]? Emails {get; set;}

    [JsonPropertyName("key")]
    public string? Key {get; set;}

    // empty constructor bc of some JsonSerializaiton warning
    public PrivateKey(){}

    public PrivateKey(string[] emails, string key) {
        Emails = emails;
        Key = key;
    }

    public void Add_Email(string mail) {
        if (Emails != null) {
            string[] emails_copy = new string[Emails.Length + 1];
            Array.Copy(Emails, emails_copy, Emails.Length);
            emails_copy[^1] = mail;
            Emails = emails_copy;
        } else {
            Emails = new string[] {mail};
        }
    }
}

/**
* Class for representing messages
*/
public class MessageObject {

    [JsonPropertyName("email")]
    public string? Email {get; set;}

    [JsonPropertyName("content")]
    public string? Content {get; set;}

    // empty constructor bc of JsonSerialization warning
    public MessageObject(){}

    public MessageObject(string mail, string contents) {
        Email = mail;
        Content = contents;
    }
}

/**
* Helper class for methods that drive each of the functionalities of the program
*/
public static class Helpers {

    // shared Http client, base URLs, key filepaths
    private static readonly HttpClient client = new();
    private static readonly string message_url = @"server/Message/";
    private static readonly string key_url = @"server/Key/";
    private static readonly string public_path = "public.key";
    private static readonly string private_path = "private.key";

    // write key to specified file
    public static void WriteKey(string path, string info) {
        using StreamWriter writer = new(path);
        writer.WriteLine(info);
    }

    // get response from URL
    private static async Task<string> CallURL(string url) {
        var respone = client.GetStringAsync(url);
        return await respone;
    }

    // get email's key from server
    public static void GetKey(string email) {
        string address = key_url + email;
        try {
            var response = CallURL(address);
            if (response.Result != "") {
                string path = email + ".key";
                WriteKey(path, response.Result);
            } else {
                Console.WriteLine("issue with response: did not get key");
            }
        } catch (Exception ex) {
            Console.WriteLine(ex.Message + ": did not get key");
        } 
    } 

    // generate and locally save public and private keys
    public static void GenKey(int bit_size) {
        var values = NumberFunctions.GenerateKeys(bit_size);
        var formatted_keys = NumberFunctions.FormatKeys(values.Item1, values.Item2, values.Item3);
        PublicKey public_key = new(null, formatted_keys.Item1);
        PrivateKey private_key = new(Array.Empty<string>(), formatted_keys.Item2);
        string json_public = JsonSerializer.Serialize(public_key);
        string json_private = JsonSerializer.Serialize(private_key);
        WriteKey("public.key", json_public);
        WriteKey("private.key", json_private);
    }

    // push public key of email to server
    public static async Task PushKey(string email, PublicKey key) {
        string address = key_url + email;
        var content = new StringContent(JsonSerializer.Serialize(key), Encoding.UTF8, "application/json");
        try {
            HttpResponseMessage response = await client.PutAsync(address, content);
            if (response.IsSuccessStatusCode) {
                Console.WriteLine("Key saved");
            } else {
                Console.WriteLine("Issue with request: key not saved");
            }
        } catch (Exception ex) {
            Console.WriteLine(ex.Message + ": key not saved");
        }
    }

    // send public key of email to server if available
    public static async Task SendKey(string email) { 
        try {
            string public_json = File.ReadAllText(public_path);
            string private_json = File.ReadAllText(private_path);
            var public_key = JsonSerializer.Deserialize<PublicKey>(public_json);
            var private_key = JsonSerializer.Deserialize<PrivateKey>(private_json);
            if (private_key is not null && public_key is not null) {
                public_key.Email = email;
                private_key.Add_Email(email);
                WriteKey(private_path, JsonSerializer.Serialize(private_key));
                await PushKey(email, public_key);
            } else {
                Console.WriteLine("Issue deserializing keys: key not saved");
            }
        } catch (Exception ex) {
            Console.WriteLine(ex.Message + " Key not saved");
        }
    }

    // get private key of email if available
    private static (BigInteger?, BigInteger?) CheckForPrivateKey(string email) {
        if (File.Exists("private.key")) {
            var content = File.ReadAllText("private.key");
            if (content != null && content != "") {
                PrivateKey? k = JsonSerializer.Deserialize<PrivateKey>(content);
                if (k != null) {
                    if (k.Key != null && k.Emails != null) {
                        if (Array.IndexOf(k.Emails, email) != -1) {
                            return NumberFunctions.DeriveKey(k.Key);
                        }
                    }
                }
            }
        }
        return (null, null);
    }

    // fetch msg from server of email
    public static void GetMsg(string email) {
        var decrypt_numbers = CheckForPrivateKey(email);
        if (decrypt_numbers.Item1 == null || decrypt_numbers.Item2 == null) {
            Console.WriteLine("Message can't be decoded");
            return;
        } else {
            string address = message_url + email;
        try {
            var response = CallURL(address);
            var result = response.Result;
            if (result != "") {
                MessageObject? msg = JsonSerializer.Deserialize<MessageObject>(result);
                if (msg == null) {
                    Console.WriteLine("Issue with message");
                    return;
                }
                string? message = msg.Content;
                if (message == null) {
                    Console.WriteLine("Issue with message");
                    return;
                }
                string decrypted_msg = NumberFunctions.Decrypt((BigInteger) decrypt_numbers.Item1, (BigInteger) decrypt_numbers.Item2, message);
                Console.WriteLine(decrypted_msg);
            } else {
                Console.WriteLine("Issue with response");
            }
        } catch (Exception ex) {
            Console.WriteLine(ex.Message + ": message not gotten");
        } 
        }
    }

    // push msg to server for email
    public static async Task PushMsg(string email, MessageObject msg) {
        string address = message_url + email;
        var content = new StringContent(JsonSerializer.Serialize(msg), Encoding .UTF8, "application/json");
        try {
            HttpResponseMessage response = await client.PutAsync(address, content);
            if (response.IsSuccessStatusCode) {
                Console.WriteLine("Message written");
            }
        } catch (Exception ex) {
            Console.WriteLine(ex.Message + ": message not written");
        }
    }

    // send msg if you have public key
    public static async Task SendMsg(string email, string msg) {
        if (File.Exists(email + ".key")) {
            PublicKey? public_key = JsonSerializer.Deserialize<PublicKey>(File.ReadAllText(email + ".key"));
            if (public_key == null) {
                Console.WriteLine("issue deserializing key");
                return;
            }
            if (public_key.Key == null) {
                Console.WriteLine("issue with key");
                return;
            }
            var values = NumberFunctions.DeriveKey(public_key.Key);
            string encrypted_msg = NumberFunctions.Encrypt(values.Item1, values.Item2, msg);
            MessageObject messageObjectmessage = new MessageObject(email, encrypted_msg);
            await PushMsg(email, messageObjectmessage);
        } else {
            Console.WriteLine(string.Format("Key does not exist for {0}", email)); 
        }
    }
}

/**
* Driver class
*/
class Program {

    // program help message
    static void PrintHelpMessage(){
        Console.WriteLine(@"dotnet run <option> <other arguments>");
    }

    /**
    * Check if arguments are valid
    * Return code indicating which functionality to run
    */
    static int HandleArgs(string[] s){
        if (s.Length == 0) {
            PrintHelpMessage();
            return 0;
        }
        else if (s[0] == "keyGen") {
            if (s.Length == 2) {
                if (int.TryParse(s[1], out int result)) {
                    if (result > 0) {
                        return 1;
                    } else {
                        Console.WriteLine("Bit length for not valid");
                        return 0;
                    }
                }
            }
            Console.WriteLine("usage: dotnet run keyGen <keysize in bits>");
            return 0;
        }
        else if (s[0] == "sendKey") {
            if (s.Length == 2) {
                return 2;
            } else {
                Console.WriteLine("usage: dotnet sendKey <email>");
                return 0;
            }
        }
        else if (s[0] == "getKey") {
            if (s.Length == 2) {
                return 3;
            } else {
                Console.WriteLine("usage: dotnet run getKey <email>");
                return 0;
            }
        }
        else if (s[0] == "sendMsg") {
            if (s.Length == 3) {
                return 4;
            } else {
                Console.WriteLine("usage: dotnet run sendMsg <recipient email> <message string>");
                return 0;
            }
        }
        else if (s[0] == "getMsg") {
            if (s.Length == 2) {
                return 5;
            } else {
                Console.WriteLine("usage: dotnet run getMsg <email>");
                return 0;
            }
        }
        else {
            PrintHelpMessage();
            return 0;
        }
    }

    /**
    * Check commandline args and then run main program logic
    */
    static async Task Main(string[] args){
        int code = HandleArgs(args);
        if (code == 0) {
            return;
        } else if (code == 1) {
            Helpers.GenKey(int.Parse(args[1]));
        } else if (code == 2) {
            await Helpers.SendKey(args[1]);
        } else if (code == 3) {
            Helpers.GetKey(args[1]);
        } else if (code == 4) {
            await Helpers.SendMsg(args[1], args[2]);
        } else {
            Helpers.GetMsg(args[1]);
        }
    }
}

}