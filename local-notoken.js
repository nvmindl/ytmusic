const os = require('os');

process.env.LOCAL_NO_TOKEN = '1';
process.env.PREFER_HLS_AUDIO = '1';
process.env.HLS_AUDIO_ONLY = '0';
process.env.HLS_USE_ACCOUNT_AUTH = '0';
process.env.RETURN_DIRECT_AUDIO_URLS = '1';
process.env.PREPARE_STREAM_TRACKS = '0';
process.env.WARM_STREAM_TRACKS = '0';
process.env.PORT = process.env.PORT || '3114';

const port = process.env.PORT;
const addresses = [];

for (const entries of Object.values(os.networkInterfaces())) {
  for (const entry of entries || []) {
    if (entry.family === 'IPv4' && !entry.internal) {
      addresses.push(entry.address);
    }
  }
}

console.log('\nLocal no-token mode enabled.');
console.log(`Install on this PC: http://localhost:${port}/manifest.json`);
for (const address of addresses) {
  console.log(`Install on same Wi-Fi/LAN: http://${address}:${port}/manifest.json`);
}
console.log('');

require('./index');
