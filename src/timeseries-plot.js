// Plotly is provided by the app entry before this module loads.
const Plotly = window.Plotly;

// Constants
const GRAPH_DIV = 'graph';
const LABEL_NAME = 'Label';
const TEXT_COLOR_DARK = '#ccc';
const TEXT_COLOR_LIGHT = '#333';
const MAX_CHANNELS = 400;
var config = {
   responsive: true,
   toImageButtonOptions: {
      width: window.innerWidth,
      height: window.innerHeight
   },
   displaylogo: false,
   scrollZoom: true,
   modeBarButtonsToRemove: ['hoverClosestCartesian', 'hoverCompareCartesian', 'lasso2d', 'toggleSpikelines']
};
const zoomedOut = { xaxis: { autorange: true, }, yaxis: { autorange: true } };
const types = [{ type: 'scatter', mode: 'lines' }, { type: 'scatter', mode: 'markers' }, { type: 'bar' }, { type: 'box' }, { type: 'histogram' }];

const storage = {
   getItem: (name) => {
      // console.log(`Reading ${name} from storage`);
      try {
         return localStorage.getItem(name);
      }
      catch {
         return null;
      }
   },
   setItem: (name, value) => {
      // console.log(`Saving ${name} to storage`);
      try {
         localStorage.setItem(name, value);
      }
      catch {
      }
   },
   removeItem: (name) => {
      try {
         localStorage.removeItem(name);
      }
      catch {
      }
   }
}

// State
var legend = '';
var state = [zoomedOut];
var channels = [];
var modeChannels = [];
var existingFiles = [];
var hidden = new Set();
var stacked = storage.getItem('stacked') === true.toString();
var metadata = false;
var zen = false;
var currentType = 0;
var showHiddenChannelsInLegend = true;
var showLegend = storage.getItem('legend') !== 'false';
var shapeIndex = -1;
var darkTheme = storage.getItem('theme') !== 'light';
var showRangeslider = storage.getItem('rangeslider') === 'true';
var deferredPrompt = null;
var plotOptions = {};
// var errorLog = [];
const colorParams = { color: darkTheme ? TEXT_COLOR_DARK : TEXT_COLOR_LIGHT };
const themeDark = {
   paper_bgcolor: '#222',
   plot_bgcolor: '#222',
   xaxis: { tickfont: { color: TEXT_COLOR_DARK } },
   yaxis: { tickfont: { color: TEXT_COLOR_DARK } },
   legend: { font: { color: TEXT_COLOR_DARK } },
   title: { font: { color: '#ddd' }, text: '' },
};
const themeLight = {
   paper_bgcolor: '#fff',
   plot_bgcolor: '#fff',
   xaxis: { tickfont: { color: TEXT_COLOR_LIGHT } },
   yaxis: { tickfont: { color: TEXT_COLOR_LIGHT } },
   legend: { font: { color: TEXT_COLOR_LIGHT } },
   title: { font: { color: '#222' }, text: '' },
};
for (let axis = 1; axis < MAX_CHANNELS; axis++) {    // TODO: move to somewhere else?!? dependent on number of channels as well
   themeDark['yaxis' + axis] = { tickfont: { color: TEXT_COLOR_DARK } };
   themeLight['yaxis' + axis] = { tickfont: { color: TEXT_COLOR_LIGHT } };
}

var layout = darkTheme ? { ...themeDark, showlegend: showLegend } : { ...themeLight, showlegend: showLegend };
var tabs = [];
var files_db;
var data = [];

var quickActionIndex = 0;
let hash;

const hideLoader = () => {
   var x = document.getElementById("loader");
   x.style.display = "none";
}

const showLoader = () => {
   var x = document.getElementById("loader");
   x.style.display = "block";
}

const isBusy = () => {
   var x = document.getElementById("loader");
   return x.style.display === "block";
}

const setTitle = (title) => {
   legend = title || '';
   layout = { ...layout, title: { ...(layout.title || {}), text: legend } };
   const graph = document.getElementById(GRAPH_DIV);
   if (graph && graph._fullLayout) {
      Plotly.relayout(GRAPH_DIV, layout);
   }

   if (title && title !== '') {
      title = `Xplot - ${title}`;
   } else {
      title = 'Xplot';
   }

   document.title = title;
   // document.getElementById('title').innerText = title;
}

const doWork = (callback) => {
   // TODO: improve doWork to handle being called within another doWork...
   const wrapperFunc = () => {
      try {
         callback();
      }
      catch (err) {
         console.warn(err);
      }

      hideLoader();
   }

   // if (isBusy()) {
   //    callback();
   // } else {
   showLoader();
   setTimeout(wrapperFunc, 10);
   // }
}

const sendNotification = (message) => {
   if (Notification.permission === "granted") {
      var notification = new Notification(message);
   }
   else if (Notification.permission !== "denied") {
      Notification.requestPermission().then(function (permission) {
         if (permission === "granted") {
            var notification = new Notification(message);
         }
      });
   }
}

const installApp = async () => {
   if (deferredPrompt !== null) {
      deferredPrompt.prompt();
      const { outcome } = await deferredPrompt.userChoice;
      if (outcome === 'accepted') {
         deferredPrompt = null;
      }
   }
}

/**
* Secure Hash Algorithm (SHA256)
* http://www.webtoolkit.info/
* Original code by Angel Marin, Paul Johnston
**/
function SHA256(s) {
   var chrsz = 8;
   var hexcase = 0;

   function safe_add(x, y) {
      var lsw = (x & 0xFFFF) + (y & 0xFFFF);
      var msw = (x >> 16) + (y >> 16) + (lsw >> 16);
      return (msw << 16) | (lsw & 0xFFFF);
   }

   function S(X, n) { return (X >>> n) | (X << (32 - n)); }
   function R(X, n) { return (X >>> n); }
   function Ch(x, y, z) { return ((x & y) ^ ((~x) & z)); }
   function Maj(x, y, z) { return ((x & y) ^ (x & z) ^ (y & z)); }
   function Sigma0256(x) { return (S(x, 2) ^ S(x, 13) ^ S(x, 22)); }
   function Sigma1256(x) { return (S(x, 6) ^ S(x, 11) ^ S(x, 25)); }
   function Gamma0256(x) { return (S(x, 7) ^ S(x, 18) ^ R(x, 3)); }
   function Gamma1256(x) { return (S(x, 17) ^ S(x, 19) ^ R(x, 10)); }

   function core_sha256(m, l) {
      var K = new Array(0x428A2F98, 0x71374491, 0xB5C0FBCF, 0xE9B5DBA5, 0x3956C25B, 0x59F111F1, 0x923F82A4, 0xAB1C5ED5, 0xD807AA98, 0x12835B01, 0x243185BE, 0x550C7DC3, 0x72BE5D74, 0x80DEB1FE, 0x9BDC06A7, 0xC19BF174, 0xE49B69C1, 0xEFBE4786, 0xFC19DC6, 0x240CA1CC, 0x2DE92C6F, 0x4A7484AA, 0x5CB0A9DC, 0x76F988DA, 0x983E5152, 0xA831C66D, 0xB00327C8, 0xBF597FC7, 0xC6E00BF3, 0xD5A79147, 0x6CA6351, 0x14292967, 0x27B70A85, 0x2E1B2138, 0x4D2C6DFC, 0x53380D13, 0x650A7354, 0x766A0ABB, 0x81C2C92E, 0x92722C85, 0xA2BFE8A1, 0xA81A664B, 0xC24B8B70, 0xC76C51A3, 0xD192E819, 0xD6990624, 0xF40E3585, 0x106AA070, 0x19A4C116, 0x1E376C08, 0x2748774C, 0x34B0BCB5, 0x391C0CB3, 0x4ED8AA4A, 0x5B9CCA4F, 0x682E6FF3, 0x748F82EE, 0x78A5636F, 0x84C87814, 0x8CC70208, 0x90BEFFFA, 0xA4506CEB, 0xBEF9A3F7, 0xC67178F2);
      var HASH = new Array(0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19);
      var W = new Array(64);
      var a, b, c, d, e, f, g, h, i, j;
      var T1, T2;

      m[l >> 5] |= 0x80 << (24 - l % 32);
      m[((l + 64 >> 9) << 4) + 15] = l;

      for (var i = 0; i < m.length; i += 16) {
         a = HASH[0];
         b = HASH[1];
         c = HASH[2];
         d = HASH[3];
         e = HASH[4];
         f = HASH[5];
         g = HASH[6];
         h = HASH[7];

         for (var j = 0; j < 64; j++) {
            if (j < 16) W[j] = m[j + i];
            else W[j] = safe_add(safe_add(safe_add(Gamma1256(W[j - 2]), W[j - 7]), Gamma0256(W[j - 15])), W[j - 16]);

            T1 = safe_add(safe_add(safe_add(safe_add(h, Sigma1256(e)), Ch(e, f, g)), K[j]), W[j]);
            T2 = safe_add(Sigma0256(a), Maj(a, b, c));

            h = g;
            g = f;
            f = e;
            e = safe_add(d, T1);
            d = c;
            c = b;
            b = a;
            a = safe_add(T1, T2);
         }

         HASH[0] = safe_add(a, HASH[0]);
         HASH[1] = safe_add(b, HASH[1]);
         HASH[2] = safe_add(c, HASH[2]);
         HASH[3] = safe_add(d, HASH[3]);
         HASH[4] = safe_add(e, HASH[4]);
         HASH[5] = safe_add(f, HASH[5]);
         HASH[6] = safe_add(g, HASH[6]);
         HASH[7] = safe_add(h, HASH[7]);
      }
      return HASH;
   }

   function str2binb(str) {
      var bin = Array();
      var mask = (1 << chrsz) - 1;
      for (var i = 0; i < str.length * chrsz; i += chrsz) {
         bin[i >> 5] |= (str.charCodeAt(i / chrsz) & mask) << (24 - i % 32);
      }
      return bin;
   }

   function Utf8Encode(string) {
      string = string.replace(/\r\n/g, '\n');
      var utftext = '';

      for (var n = 0; n < string.length; n++) {

         var c = string.charCodeAt(n);

         if (c < 128) {
            utftext += String.fromCharCode(c);
         }
         else if ((c > 127) && (c < 2048)) {
            utftext += String.fromCharCode((c >> 6) | 192);
            utftext += String.fromCharCode((c & 63) | 128);
         }
         else {
            utftext += String.fromCharCode((c >> 12) | 224);
            utftext += String.fromCharCode(((c >> 6) & 63) | 128);
            utftext += String.fromCharCode((c & 63) | 128);
         }

      }

      return utftext;
   }

   function binb2hex(binarray) {
      var hex_tab = hexcase ? '0123456789ABCDEF' : '0123456789abcdef';
      var str = '';
      for (var i = 0; i < binarray.length * 4; i++) {
         str += hex_tab.charAt((binarray[i >> 2] >> ((3 - i % 4) * 8 + 4)) & 0xF) +
            hex_tab.charAt((binarray[i >> 2] >> ((3 - i % 4) * 8)) & 0xF);
      }
      return str;
   }

   s = Utf8Encode(s);
   return binb2hex(core_sha256(str2binb(s), s.length * chrsz));
}

const parseCsv = (csvText) => {
   let rows = csvText.split('\n');
   const checks = [rows[0].split(',').length, rows[0].split(';').length, rows[0].split('\t').length];
   let separator = ',';
   if (checks[1] > checks[0]) separator = ';';
   if (checks[2] > checks[0] && checks[2] > checks[1]) separator = '\t';
   let chans = rows[0].split(separator).map(c => c.trim().replace(/^\"*|"*$/gm, ''));  // TODO: handle quoted ("") column names!
   rows.splice(0, 1);
   let columns = chans.map(_ => []);
   rows.forEach((row, _n) => {  // TODO: handle sub sampling (or averaging, min/max)
      if (row.length > 0) {
         const values = row.split(separator);
         for (let i = 0; i < columns.length; i++) {
            columns[i].push(values[i].replace(',', '.').replace('\r', '').replace(/^\"*|"*$/gm, ''));
         }
      }
   });

   columns[0] = columns[0].map(t => new Date(Date.parse(t)));
   chans.splice(0, 1);

   return { channels: chans, columns: columns };
}

function arrayToAscii(array, start, length) {
   var str = "";
   for (var i = 0; i < length; i++) {
      str += String.fromCharCode(array[start + i]);
   }
   return str.trim();
}

function flipBits(n) {
   return parseInt(n.toString(2).split('').map(bit => 1 - bit).join(''), 2)
}

class EDF {


   constructor(uint8array) {
      var pos = 0;

      var buf = uint8array;
      this.bytes = uint8array;

      this.header = arrayToAscii(buf, pos, 8); pos += 8;
      this.patient = arrayToAscii(buf, pos, 80); pos += 80;
      this.info = arrayToAscii(buf, pos, 80); pos += 80;
      this.date = arrayToAscii(buf, pos, 8); pos += 8;
      this.time = arrayToAscii(buf, pos, 8); pos += 8;
      this.header_bytes = arrayToAscii(buf, pos, 8); pos += 8;
      this.data_format = arrayToAscii(buf, pos, 44); pos += 44;
      this.data_records = parseInt(arrayToAscii(buf, pos, 8)); pos += 8;
      this.data_record_duration = parseFloat(arrayToAscii(buf, pos, 8)); pos += 8;
      this.channelCount = parseInt(arrayToAscii(buf, pos, 4)); pos += 4;

      this.duration = this.data_record_duration * this.data_records;
      this.bytes_per_sample = this.header == "0" ? 2 : 3;
      this.has_annotations = false;

      var n = this.channelCount;



      this.channels = [];
      for (var i = 0; i < n; i++) {
         var channel = new Object();
         channel.label = arrayToAscii(buf, pos, 16); pos += 16;
         channel.data = [];

         // console.log("CHANNEL", i, channel.label);
         if (channel.label.indexOf("DF Annotations") > 0) {
            this.has_annotations = true;

         }
         this.channels.push(channel);
      }

      // console.log("CHANNELS", n);

      this.realChannelCount = n;
      if (this.has_annotations) {
         this.realChannelCount--;
      }

      this.annotation_bytes = 0;

      // console.log("REAL CHANNELS", this.realChannelCount);

      for (var i = 0; i < n; i++) {
         this.channels[i].transducer = arrayToAscii(buf, pos, 80); pos += 80;
      }

      for (var i = 0; i < n; i++) {
         this.channels[i].dimensions = arrayToAscii(buf, pos, 8); pos += 8;
      }

      for (var i = 0; i < n; i++) {
         this.channels[i].phys_min = parseInt(arrayToAscii(buf, pos, 8)); pos += 8;
      }

      for (var i = 0; i < n; i++) {
         this.channels[i].phys_max = parseInt(arrayToAscii(buf, pos, 8)); pos += 8;
      }

      for (var i = 0; i < n; i++) {
         this.channels[i].digital_min = parseInt(arrayToAscii(buf, pos, 8)); pos += 8;
      }

      for (var i = 0; i < n; i++) {
         this.channels[i].digital_max = parseInt(arrayToAscii(buf, pos, 8)); pos += 8;
      }

      for (var i = 0; i < n; i++) {
         this.channels[i].prefilters = arrayToAscii(buf, pos, 80); pos += 80;
      }

      for (var i = 0; i < n; i++) {
         this.channels[i].num_samples = parseInt(arrayToAscii(buf, pos, 8)); pos += 8;
         if (this.has_annotations && i == this.realChannelCount) {
            this.annotation_bytes = this.channels[i].num_samples * 2;
         }
      }

      for (var i = 0; i < n; i++) {
         /*edf["channels"][i].reserved = arrayToAscii(buf, pos, 32);*/
         this.channels[i].k = (this.channels[i].phys_max - this.channels[i].phys_min) / (this.channels[i].digital_max - this.channels[i].digital_min);
         // console.log("F for", i, this.channels[i].k);
         pos += 32;
      }


      this.sampling_rate = this.channels[0].num_samples * this.data_record_duration;
      this.sample_size = 0;

      // console.log("ANN BYTES", this.annotation_bytes);

      if (this.has_annotations) {
         this.sample_size = (n - 1) * 2 * this.sampling_rate + 60 * 2;
      }
      else {
         this.sample_size = (n) * 2 * this.sampling_rate;
      }

      var duration = (buf.length - pos) / this.sample_size;

      this.headerOffset = pos;

      this.samples_in_one_data_record = this.sampling_rate * this.data_record_duration;


      for (var j = 0; j < this.data_records; j++) {
         for (var i = 0; i < this.realChannelCount; i++) {
            var koef = this.channels[i].k;


            for (var k = 0; k < this.samples_in_one_data_record; k++) {
               if (this.bytes_per_sample == 2) {
                  var b1 = buf[pos]; pos++;
                  var b2 = buf[pos]; pos++;

                  var val = (b2 << 8) + b1;

                  if (b2 >> 7 == 1) {
                     val = -flipBits(val) - 1;
                  }
                  this.channels[i].data.push(val * koef);
               }
               else if (this.bytes_per_sample == 3) {
                  var b1 = buf[pos]; pos++;
                  var b2 = buf[pos]; pos++;
                  var b3 = buf[pos]; pos++;

                  var val = (b3 << 16) + (b2 << 8) + b1;

                  if (b3 >> 7 == 1) {
                     val = -flipBits(val) - 1;
                  }
                  this.channels[i].data.push(val * koef);
               }
            }
         }

         if (this.has_annotations) {
            var ann = arrayToAscii(buf, pos, this.annotation_bytes); pos += this.annotation_bytes;
            // TODO: parse annotations to its own channel??? console.log("ANN", ann);
         }
      }
   }

   readSingleChannel(channel, startSecond, lengthSeconds) {
      var startSample = startSecond * this.sampling_rate;
      var endSample = startSample + lengthSeconds * this.sampling_rate;

      if (endSample > this.maxSample) {
         endSample = this.maxSample;
      }

      var data = [];

      var ch = this.channels[channel].data;
      for (var i = startSample; i < endSample; i++) {
         data.push(ch[i]);
      }

      return data;
   }


   read(startSecond, lengthSeconds) {
      var array = [];

      // console.log(this.realChannelCount, "REAL");

      for (var i = 0; i < this.realChannelCount; i++) {
         array.push(this.readSingleChannel(i, startSecond, lengthSeconds));
      }

      return array;
   }

}

const setConfig = options => {
   const { hideOpen, hideMetadata } = options;
   config = {
      responsive: true,
      toImageButtonOptions: {
         width: window.innerWidth,
         height: window.innerHeight
      },
      displayModebar: true,
      scrollZoom: true,
      displaylogo: false,
      modeBarButtonsToRemove: ['hoverClosestCartesian', 'hoverCompareCartesian', 'lasso2d', 'toggleSpikelines'],
      modeBarButtonsToAdd: [...(hideOpen === true ? [] : [{
         name: 'Open CSV file (O)',
         icon: {
            width: 448,
            height: 512,
            path: 'M224 136V0H24C10.7 0 0 10.7 0 24v464c0 13.3 10.7 24 24 24h336c13.3 0 24-10.7 24-24V160H248c-13.2 0-24-10.8-24-24zm-64 268c0 10.7-12.9 16-20.5 8.5L104 376H76c-6.6 0-12-5.4-12-12v-56c0-6.6 5.4-12 12-12h28l35.5-36.5c7.6-7.6 20.5-2.2 20.5 8.5v136zm33.2-47.6c9.1-9.3 9.1-24.1 0-33.4-22.1-22.8 12.2-56.2 34.4-33.5 27.2 27.9 27.2 72.4 0 100.4-21.8 22.3-56.9-10.4-34.4-33.5zm86-117.1c54.4 55.9 54.4 144.8 0 200.8-21.8 22.4-57-10.3-34.4-33.5 36.2-37.2 36.3-96.5 0-133.8-22.1-22.8 12.3-56.3 34.4-33.5zM384 121.9v6.1H256V0h6.1c6.4 0 12.5 2.5 17 7l97.9 98c4.5 4.5 7 10.6 7 16.9z'
         },
         click: () => {
            const fileElem = document.getElementById("fileElem");
            if (fileElem) {
               fileElem.click();
            }
         }
      }]), ...[{
         name: 'Download plot data as CSV (E)',
         icon: {
            width: 448,
            height: 512,
            path: 'M224 136V0H24C10.7 0 0 10.7 0 24v464c0 13.3 10.7 24 24 24h336c13.3 0 24-10.7 24-24V160H248c-13.2 0-24-10.8-24-24zm76.45 211.36l-96.42 95.7c-6.65 6.61-17.39 6.61-24.04 0l-96.42-95.7C73.42 337.29 80.54 320 94.82 320H160v-80c0-8.84 7.16-16 16-16h32c8.84 0 16 7.16 16 16v80h65.18c14.28 0 21.4 17.29 11.27 27.36zM377 105L279.1 7c-4.5-4.5-10.6-7-17-7H256v128h128v-6.1c0-6.3-2.5-12.4-7-16.9z'
            // path: 'M433.941 129.941l-83.882-83.882A48 48 0 0 0 316.118 32H48C21.49 32 0 53.49 0 80v352c0 26.51 21.49 48 48 48h352c26.51 0 48-21.49 48-48V163.882a48 48 0 0 0-14.059-33.941zM224 416c-35.346 0-64-28.654-64-64 0-35.346 28.654-64 64-64s64 28.654 64 64c0 35.346-28.654 64-64 64zm96-304.52V212c0 6.627-5.373 12-12 12H76c-6.627 0-12-5.373-12-12V108c0-6.627 5.373-12 12-12h228.52c3.183 0 6.235 1.264 8.485 3.515l3.48 3.48A11.996 11.996 0 0 1 320 111.48z'
         },
         click: downloadCsv
      }, {
         name: 'Toggle stack mode (S)',
         icon: {
            width: 512,
            height: 512,
            path: 'M496 384H64V80c0-8.84-7.16-16-16-16H16C7.16 64 0 71.16 0 80v336c0 17.67 14.33 32 32 32h464c8.84 0 16-7.16 16-16v-32c0-8.84-7.16-16-16-16zM464 96H345.94c-21.38 0-32.09 25.85-16.97 40.97l32.4 32.4L288 242.75l-73.37-73.37c-12.5-12.5-32.76-12.5-45.25 0l-68.69 68.69c-6.25 6.25-6.25 16.38 0 22.63l22.62 22.62c6.25 6.25 16.38 6.25 22.63 0L192 237.25l73.37 73.37c12.5 12.5 32.76 12.5 45.25 0l96-96 32.4 32.4c15.12 15.12 40.97 4.41 40.97-16.97V112c.01-8.84-7.15-16-15.99-16z'
         },
         click: toggleStack
      }, {
         name: 'Toggle legend format (L)',
         icon: {
            width: 512,
            height: 512,
            path: 'M496 384H160v-16c0-8.8-7.2-16-16-16h-32c-8.8 0-16 7.2-16 16v16H16c-8.8 0-16 7.2-16 16v32c0 8.8 7.2 16 16 16h80v16c0 8.8 7.2 16 16 16h32c8.8 0 16-7.2 16-16v-16h336c8.8 0 16-7.2 16-16v-32c0-8.8-7.2-16-16-16zm0-160h-80v-16c0-8.8-7.2-16-16-16h-32c-8.8 0-16 7.2-16 16v16H16c-8.8 0-16 7.2-16 16v32c0 8.8 7.2 16 16 16h336v16c0 8.8 7.2 16 16 16h32c8.8 0 16-7.2 16-16v-16h80c8.8 0 16-7.2 16-16v-32c0-8.8-7.2-16-16-16zm0-160H288V48c0-8.8-7.2-16-16-16h-32c-8.8 0-16 7.2-16 16v16H16C7.2 64 0 71.2 0 80v32c0 8.8 7.2 16 16 16h208v16c0 8.8 7.2 16 16 16h32c8.8 0 16-7.2 16-16v-16h208c8.8 0 16-7.2 16-16V80c0-8.8-7.2-16-16-16z'
         },
         click: toggleLegend
      }], ...(hideMetadata === true ? [] : [{
         name: 'Toggle metadata (M)',
         icon: {
            width: 384,
            height: 512,
            path: 'M224 136V0H24C10.7 0 0 10.7 0 24v464c0 13.3 10.7 24 24 24h336c13.3 0 24-10.7 24-24V160H248c-13.2 0-24-10.8-24-24zm64 236c0 6.6-5.4 12-12 12H108c-6.6 0-12-5.4-12-12v-8c0-6.6 5.4-12 12-12h168c6.6 0 12 5.4 12 12v8zm0-64c0 6.6-5.4 12-12 12H108c-6.6 0-12-5.4-12-12v-8c0-6.6 5.4-12 12-12h168c6.6 0 12 5.4 12 12v8zm0-72v8c0 6.6-5.4 12-12 12H108c-6.6 0-12-5.4-12-12v-8c0-6.6 5.4-12 12-12h168c6.6 0 12 5.4 12 12zm96-114.1v6.1H256V0h6.1c6.4 0 12.5 2.5 17 7l97.9 98c4.5 4.5 7 10.6 7 16.9z'
         },
         click: toggleMetadata
      }, {
         name: 'Download metadata',
         icon: {
            width: 448,
            height: 512,
            path: 'M0 32v448h448V32H0zm243.8 349.4c0 43.6-25.6 63.5-62.9 63.5-33.7 0-53.2-17.4-63.2-38.5l34.3-20.7c6.6 11.7 12.6 21.6 27.1 21.6 13.8 0 22.6-5.4 22.6-26.5V237.7h42.1v143.7zm99.6 63.5c-39.1 0-64.4-18.6-76.7-43l34.3-19.8c9 14.7 20.8 25.6 41.5 25.6 17.4 0 28.6-8.7 28.6-20.8 0-14.4-11.4-19.5-30.7-28l-10.5-4.5c-30.4-12.9-50.5-29.2-50.5-63.5 0-31.6 24.1-55.6 61.6-55.6 26.8 0 46 9.3 59.8 33.7L368 290c-7.2-12.9-15-18-27.1-18-12.3 0-20.1 7.8-20.1 18 0 12.6 7.8 17.7 25.9 25.6l10.5 4.5c35.8 15.3 55.9 31 55.9 66.2 0 37.8-29.8 58.6-69.7 58.6z'
         },
         click: downloadMetadata
      }])
      ]
   };
}

const mergePlotData = csvText => {
   doWork(() => {
      const csv = parseCsv(csvText);
      let _channels = csv.channels;
      let columns = csv.columns;

      // Remove possible channel duplicates (TODO: merge data into existing data if duplicate?)
      for (let index in _channels) {
         let channel = _channels[index];
         let num = 1;
         while (channels.some(c => c === channel)) {
            channel = channel.replace(new RegExp('[0-9]+$'), '') + num;
            _channels[index] = channel;
            num++;
         }
      }

      const _data = _channels.map((ch, i) => {
         return {
            x: columns[0],       // TODO: filter gaps
            y: columns[i + 1],   // TODO: filter gaps
            type: 'scatter',
            name: _channels[i]
         };
      });

      channels = [...channels, ..._channels];
      data = [...data, ..._data];

      buildModes();

      if (stacked) {
         stack();
      }
      else {
         unstack();
      }
   });
}

const bindPlotEvents = (gd) => {
   if (!gd || typeof gd.on !== 'function') {
      return;
   }
   if (typeof gd.removeAllListeners === 'function') {
      gd.removeAllListeners('plotly_relayout');
      gd.removeAllListeners('plotly_restyle');
      gd.removeAllListeners('plotly_afterplot');
   }
   gd.on('plotly_relayout', relayout);
   gd.on('plotly_restyle', restyle);
   gd.on('plotly_afterplot', hideLoader);
};

const loadAndPlotDataSync = (csvText) => {
   const csv = parseCsv(csvText);
   channels = csv.channels;
   let columns = csv.columns;

   data = channels.map((ch, i) => {
      return {
         x: columns[0].filter((_t, n) => columns[i + 1][n] !== ''),  // filter gaps
         y: columns[i + 1].filter((c, n) => c !== ''), // filter gaps
         type: 'scatter',
         mode: 'lines',
         name: channels[i]
      };
   });

   buildModes();

   setConfig(plotOptions);

   // The empty startup plot reports a numeric axis range. Keep that range from
   // pinning the next file to 1970, and fit each newly opened file.
   const xaxis = { ...(layout.xaxis || {}) };
   const yaxis = { ...(layout.yaxis || {}) };
   delete xaxis.range;
   delete yaxis.range;
   layout = { ...layout, xaxis: { ...xaxis, autorange: true }, yaxis: { ...yaxis, autorange: true } };

   const t = new Date();
   log('BEGIN newPlot: ');
   Plotly.newPlot(GRAPH_DIV, data, layout, config)
      .then((gd) => {
         bindPlotEvents(gd);
         log(`END newPlot: ${new Date() - t}`);
         if (stacked) {  // TODO: see if updateUI is needed to be called in other cases as well
            updateUI();
            stack();
         }
         // console.log('done plotting');
      });

   if (!plotOptions.share) {
      checkCreateThumbnail();
   }
}

const checkCreateThumbnail = () => {
   if (plotOptions.thumbnail === '1') {
      layout = {
         ...layout,
         showlegend: false,
         margin: {
            l: 20,
            r: 10,
            b: 25,
            t: 40,
            pad: 4
         },
      };
      Plotly.update(GRAPH_DIV, {}, layout).then(() => {
         Plotly.toImage(GRAPH_DIV, { format: 'png' /*svg better but to slow?*/, width: 400, height: 300 }).then((url) => {
            const link = window.location.href.replace('thumbnail=1', '').replace('?&', '?').replace('&&', '&');
            document.getElementById(GRAPH_DIV).innerHTML = '<a href="' + link + '"><img id="thumbnail" src="' + url + '" /></a>';
            document.getElementById('thumbnail').src = url;

            const metaTags = document.getElementsByTagName('meta');
            let metaOgImage = null;
            let metaTwitterImage = null;
            for (let i = 0; i < metaTags.length; i++) {
               if (metaTags[i].getAttribute('property') === 'og:image') {
                  metaOgImage = metaTags[i];
               } else if (metaTags[i].getAttribute('property') === 'twitter:image') {
                  metaTwitterImage = metaTags[i];
               }
            }

            if (!metaOgImage) {
               metaOgImage = document.createElement('meta')
               metaOgImage.setAttribute('property', 'og:image');
               document.getElementsByTagName('head')[0].appendChild(metaOgImage);
            }

            if (!metaTwitterImage) {
               metaTwitterImage = document.createElement('meta')
               metaTwitterImage.setAttribute('property', 'twitter:image');
               document.getElementsByTagName('head')[0].appendChild(metaTwitterImage);
            }

            metaOgImage.setAttribute('content', url);
            metaTwitterImage.setAttribute('content', url);
         });
      });
   }
}

const loadAndPlotData = csvText => {
   log('Load and plot data');
   doWork(() => loadAndPlotDataSync(csvText));

   // // TODO: build plugin generated channels
   // // const test = data.map(d => d.x.reduce((p, x, i, a) => [...p, x - p], 0));
   // const test = data.map(d => {
   //     let derivatives = [];
   //     for (let i = 1; i < d.x.length; i++) {
   //         const dt = d.x[i] - d.x[i - 1];
   //         const dy = +d.y[i] - +d.y[i - 1];
   //         const derivative = dy / (dt + 1e-10);
   //         derivatives.push(derivative);
   //     }

   //     const absSums = d.y.map(y => +y).reduce((acc, y) => acc + Math.abs(y)) / d.y.length;
   //     return derivatives.map(d => d / absSums);
   // });
   // console.log(test);
   /*
           // 1. Define plugin code
           const plugin_input = { data, metadata };
           const plugin1 = (plugin_input) => {
               // TODO: the plugin can has the input and store its output in the cache if needed...
               // console.log(metadata);
               const ch1 = { ...data[0], name: 'CH1', y: data[0].y.map(y => y * 3.14) };
               // data = [...data, ch1];
               // channels.push('CH1');
               // console.log(data);
               return [ch1];   // returns array of new channels
           }
    
           // 2. Run plugin (passing input)
           const plugin_output = plugin1({ data, metadata: getMetadata() });
    
           // 3. Process plugin output
           // TODO: put the following into the runPlugin function...
           plugin_output.map(channel => {
               channels.push(channel.name);
               data.push(channel);
           });
   */
   // TODO: sum all channel samples and normalize + downsample?

   // setConfig(plotOptions);

   // const t = new Date();
   // log('BEGIN newPlot: ');
   // Plotly.newPlot(GRAPH_DIV, data, layout, config)
   //    .then(() => {
   //       log(`END newPlot: ${new Date() - t}`);
   //       if (stacked) {  // TODO: see if updateUI is needed to be called in other cases as well
   //          updateUI();
   //          stack();
   //       }
   //       // console.log('done plotting');
   //    });
   // graph.on('plotly_relayout', relayout);
   // graph.on('plotly_restyle', restyle);
   // graph.on('plotly_afterplot', hideLoader);

}

const loadLastFileIfExisting = () => {
   hash = storage.getItem('last_file_hash');
   if (hash && files_db) {
      log('Trying to load existing file.');
      try {
         let objectStore = files_db.transaction('files_store').objectStore('files_store');
         let request = objectStore.get(+hash);
         request.onsuccess = () => {
            if (request.result) {
               setTitle(getFilename());
               loadAndPlotData(request.result.file);
               getViewsIfExisting();
               tryGetState();
            }
         };
      }
      catch (error) {
         logException(error);
      }
   }
}

const updateFileList = () => {
   let objectStore = files_db.transaction('files_store').objectStore('files_store');
   let request = objectStore.getAll();
   request.onsuccess = () => {
      if (request.result) {
         const files = request.result.map(({ id, name }) => ({ id, name })).sort((a, b) => a.name.localeCompare(b.name));
         const filesElem = document.getElementById('files');
         filesElem.innerHTML = '';
         if (files.length) {
            files.forEach(file => {
               var opt = document.createElement("option");
               opt.value = file.name;
               // opt.label = file.name;
               // opt.innerHTML = file.name;
               filesElem.appendChild(opt);
            });
         }

         existingFiles = files;
      }
   };
}

const getViewsIfExisting = () => {
   const hash = storage.getItem('last_file_hash');
   if (hash) {
      let savedViews = storage.getItem('views_' + hash);
      if (savedViews) {
         savedViews = JSON.parse(savedViews);
         savedViews.map(view => view.hidden = new Set(view.hidden));
         tabs = savedViews;
         buildTabs();

         if (tabs.length > 0) {
            const index = storage.getItem('view_current');
            if (index) {
               selectTab(+index);
               selectView(+index);
            }
         }
      }
      else {
         tabs = [];
         buildTabs();
      }
   }
}

const updateUI = () => {
   let cs = document.getElementById("checkboxStack");
   cs.checked = stacked;
   // let legend = document.getElementById("checkboxLegend");
   // legend.checked = showHiddenChannelsInLegend;
   cs = document.getElementById("checkboxMetadata");
   cs.checked = metadata;
   log('Update UI');
}

const log = (message) => {
   const rawErrorLog = storage.getItem('error_log') || "[]";
   let errorLog = JSON.parse(rawErrorLog);
   errorLog.push(message);
   if (errorLog.length > 10) {
      errorLog.splice(0, errorLog.length - 10);
   }

   storage.setItem('error_log', JSON.stringify(errorLog));
}

const logException = (ex) => {
   log(`${new Date().toUTCString()} ${ex.message} (${ex.lineNumber})`);
}

const onLoad = (options) => {
   if (darkTheme) {
      document.body.className = "dark";
      layout = { ...themeDark, showlegend: showLegend };
      log('Dark theme');
   }

   if (showRangeslider) {
      layout = { ...layout, ...{ xaxis: { ...layout.xaxis, rangeslider: { visible: showRangeslider } } } };
   }

   buildTabs();

   // When the user clicks anywhere outside of the modal, close it
   window.onclick = (event) => {
      let modal = document.getElementById("shareModal");
      if (event.target == modal) {
         modal.style.display = "none";
      }

      let menu = document.getElementById("menu");
      if (event.target == menu) {
         menu.style.display = "none";
      }

      let help = document.getElementById("helpModal");
      if (event.target == help) {
         help.style.display = "none";
      }

      let quick = document.getElementById("quickActionsModal");
      if (event.target == quick) {
         quick.style.display = "none";
      }
   }

   // window.onerror = function (message, url, lineNumber) {
   //    errorLog.push({ timestamp: new Date().toUTCString(), message, lineNumber });
   //    if (errorLog.length > 100) {
   //       errorLog.splice(0, errorLog.length - 100);
   //    }

   //    storage.push(JSON.stringify(errorLog));
   //    return true;
   // };

   // Select first tab
   let tablinks = document.getElementsByClassName("tablinks");
   for (let i = 0; i < tablinks.length; i++) {
      tablinks[i].className = tablinks[i].className.replace(" active", "");
   }
   tablinks[0].className += " active";

   try {
      let request = window.indexedDB.open('files_db', 2);
      request.onsuccess = () => {
         files_db = request.result;
         if (!options.data && !options.url && !options.share) {
            loadLastFileIfExisting();
         }

         updateFileList();
      }

      request.onupgradeneeded = e => {
         // console.log('onupgradeneeded');
         // Grab a reference to the opened database
         let db = e.target.result;

         if (e.oldVersion === 1) {
            db.deleteObjectStore('files_store');
         }

         // Create an objectStore to store our notes in (basically like a single table)
         // including a auto-incrementing key
         let objectStore = db.createObjectStore('files_store', { keyPath: 'id', autoIncrement: false });

         // Define what data items the objectStore will contain
         objectStore.createIndex('file', 'file', { unique: false });
         objectStore.createIndex('timestamp', 'timestamp', { unique: false });
         objectStore.createIndex('name', 'name', { unique: false });

        /*let objectCache = */db.createObjectStore('files_cache', { keyPath: 'id', autoIncrement: false });
         // objectStore.createIndex('file', 'file', { unique: false });
         // objectStore.createIndex('timestamp', 'timestamp', { unique: false });
         // objectStore.createIndex('name', 'name', { unique: false });
      };
   }
   catch {
      console.log('Unable to access IndexedDB');
   }

   Plotly.newPlot(GRAPH_DIV, data, layout, config).then(bindPlotEvents);
}

const hashCode = str => {
   var hash = 0, i, chr;
   for (i = 0; i < str.length; i++) {
      chr = str.charCodeAt(i);
      hash = ((hash << 5) - hash) + chr;
      hash |= 0; // convert to 32 bit integer
   }
   return hash;
};

const getShownIndices = () => channels.map((_, i) => i).filter(i => !hidden.has(i));
const getHiddenIndices = () => channels.map((_, i) => i).filter(i => hidden.has(i));

const selectTab = index => {
   let tablinks = document.getElementsByClassName("tablinks");
   for (let i = 0; i < tablinks.length; i++) {
      tablinks[i].className = tablinks[i].className.replace(" active", "");
      if (index === i) {
         tablinks[i].className += " active";
      }
   }
}

const openView = (event) => {
   let tablinks = document.getElementsByClassName("tablinks");
   let index = -1;
   for (let i = 0; i < tablinks.length; i++) {
      if (event.currentTarget === tablinks[i]) {
         index = i;
      }
   }

   selectTab(index);
   selectView(index);
}

const selectView = index => {
   // Update state
   const tab = tabs[index];
   hidden = new Set(tab.hidden);
   showHiddenChannelsInLegend = tab.showHiddenChannelsInLegend;
   stacked = tab.stacked;

   storage.setItem('view_current', index);

   // TODO: speed up changing views...
   // TODO: create state of all state variables?
   // TODO: check if localStorage should be the single source of truth for selected tab/view
   // TODO: store selected time window in view 

   // TODO: optimize legend display
   updateLegend(true, getShownIndices());
   updateLegend(false, getHiddenIndices());
   if (stacked) {
      stack();
   }
   else {
      unstack();
   }
   updateUI();
}

const runQuickAction = (e) => {
   console.log(e);
}

const getQuickActionFilterHits = () => {
   const quickActions = [
      // ['Quick actions (Ctrl+P)', () => () ],
      ['Stack/unstack plots (S)', () => toggleStack()],
      ['Show/hide menu (SPACE)', () => openMenu()],
      ['Open CSV (or Excel) file (O)', () => document.getElementById("fileElem").click()],
      ['Show/hide legend (L)', () => toggleLegend()],
      ['Append another data file (U)', () => document.getElementById("fileElem3").click()()],
      ['Show all channels (A)', () => showAllChannels()],
      ['Hide all channels (Q)', () => hideAllChannels()],
      ['Share current (visible) plot (H)', () => openShareModal()],
      ['Show help', () => openHelpModal()],
      ['Download CSV', () => downloadCsv()],
      ['Download image', () => downloadImage()],
      ['Toggle theme (T)', () => toggleTheme()],
      ['Move left (<)', () => moveLeft()],
      ['Move right (>)', () => moveRight()],
      ['Toggle range slider (R)', toggleRangeslider],
      ['Plot real-time data (J)', subscibeRealtimeData],
      // ['Toggle zen mode (Z)', () => toggleZenMode()],
   ];

   const filterElem = document.getElementById("actionFilter");
   const pattern = filterElem.value.trim().toLowerCase();
   if (pattern.length === 0) {
      return quickActions;
   }

   const result = quickActions.filter(q => q[0].toLowerCase().indexOf(pattern) !== -1)
   // const result = channels.map((ch, i) => {
   // const fixedPattern = pattern
   //    .replace('(', '\\(')
   //    .replace(')', '\\)');
   // let regex = new RegExp(fixedPattern, 'ig');
   // return [regex.test(ch), i];      
   // });
   return result;

   // const elem = document.getElementById('quickactions');
   // let items = quickActions;
   // if (searchText) {
   //    searchText = searchText.trim();
   //    items = items.filter(q => q.indexOf(searchText) !== -1);
   // }

   // items.forEach((action, i) => {
   //    var opt = document.createElement("option");
   //    opt.value = i;
   //    opt.innerHTML = action;
   //    elem.appendChild(opt);
   // });
}

const buildModes = () => {
   let modes = channels.map((_ch, i) => getModes(i));//.filer(mode => mode.length > 0);
   const modesElem = document.getElementById('modes');
   modesElem.innerHTML = '<option value="-1">-</option>';
   if (modes.length) {
      modes = modes.map((mode, i) => ({ index: i, mode: mode, name: channels[i] })).filter(m => m.mode.length > 0);
      if (modes.length) {
         modes.forEach(mode => {
            var opt = document.createElement("option");
            opt.value = mode.index;
            opt.innerHTML = mode.name;
            modesElem.appendChild(opt);
         });
      } else {
         hideShapes();
      }
   }
}

const buildTabs = () => {
   const tabsElem = document.getElementById('tabs');
   tabsElem.innerHTML = '';
   let index = 1;
   tabs.forEach(tab => {
      let btn = document.createElement('BUTTON');
      btn.innerText = 'View ' + index;
      btn.title = 'Open (' + index + ')';
      index++;
      btn.className = 'tablinks';
      btn.addEventListener('click', openView);
      tabsElem.appendChild(btn);
   });

   let btn = document.createElement('BUTTON');
   btn.innerText = ' + ';
   btn.className = 'tablinks';
   btn.title = 'Add current view';
   btn.addEventListener('click', () => addView("view " + (tabs.length + 1)));
   tabsElem.appendChild(btn);
   let btn2 = document.createElement('BUTTON');
   btn2.innerText = ' - ';
   btn2.className = 'tablinks';
   btn2.title = 'Delete selected view';
   btn2.addEventListener('click', () => deleteView());
   tabsElem.appendChild(btn2);
}

const saveViews = () => {
   const hash = storage.getItem('last_file_hash');
   const viewsObj = tabs.map(view => {
      const hidden = channels.map((_, i) => i).filter(i => view.hidden.has(i));
      return {
         ...view,
         hidden
      };
   });
   storage.setItem('views_' + hash, JSON.stringify(viewsObj));
}

const addView = name => {
   tabs.push({ name: name, hidden: new Set(hidden), stacked, showHiddenChannelsInLegend });
   buildTabs();
   saveViews();
   selectTab(tabs.length - 1);
}

const deleteView = () => {
   const tabIndex = storage.getItem('view_current');
   tabs.splice(tabIndex, 1);
   buildTabs();
   storage.removeItem('view_current');
   saveViews();
};

const updateState = ({ layout } = {}) => {
   let state = { hidden: new Set(hidden), stacked, showLegend, shapeIndex };

   if (layout && layout.xaxis.range && layout.xaxis.range.length === 2) {
      const x1 = Date.parse(layout.xaxis.range[0]);
      const x2 = Date.parse(layout.xaxis.range[1]);
      let range = [new Date(x1), new Date(x2)];
      // console.log('state = ', { range });
      state.range = range;
   }

   hash = storage.getItem('last_file_hash');
   if (hash) {
      // console.log('new state = ', state);
      storage.setItem('state_' + hash, JSON.stringify(state));
   }
}

const tryGetState = () => {
   hash = storage.getItem('last_file_hash');
   if (hash) {
      let state = storage.getItem('state_' + hash);
      if (state) {
         // console.log('state = ', JSON.parse(state));
         // // TODO: hidden = new Set(state.hidden);
         // // TODO: shapeIndex = state.shapeIndex;
         // // stacked = state.stacked;
         // // showLegend = state.showLegend;

         // if (showLegend != state.showLegend) {
         //    toggleLegend();
         // }
         // // TODO: optimize legend display

         // // TODO: update legend previous state
         // // updateLegend(true, getShownIndices());
         // // updateLegend(false, getHiddenIndices());
         // if (stacked != state.stacked) {
         //    toggleStack();
         // }

         // // TODO: take range from previous state
         // // if (state.range) {
         // //    const newLayout = { ...layout, xaxis: { ...layout.xaxis, range: state.range } };
         // //    Plotly.relayout(GRAPH_DIV, newLayout);
         // // }

         // updateUI();
      }
   }
}

// Plotly event handlers
const relayout = (e) => {
   log('relayout');
   if (!channels.length) {
      return;
   }
   if (e['xaxis.range[0]'] && e['xaxis.range[1]']) {
      layout = { ...layout, ...{ xaxis: { ...layout.xaxis, range: [e['xaxis.range[0]'], e['xaxis.range[1]']] } } };
   } else if (e['xaxis.autorange']) {
   } else {
      // console.warn('relayout without incorporating previous layout', layout, e);
      layout = { ...layout, ...e };
   }

   updateState(layout);

   state.push(layout);
   let buttonBack = document.getElementById("buttonBack");
   if (buttonBack) {
      buttonBack.disabled = state.length < 2;
   }
};

const restyle = e => {
   const v = e[0].visible;
   if (v) {
      const indices = e[1];
      if (v === true || v[0] === true) { // on
         indices.forEach(i => hidden.delete(i));
         if (stacked) { // re-stack if a new channel becomes visible
            stack();
         }
      } else if (v === 'legendonly' || v[0] === 'legendonly') { // off 
         indices.forEach(i => hidden.add(i));
         if (stacked) { // re-stack if a new channel is hidden
            stack();
         }
      }
   }
}

// Actions
function goback() {
   if (state.length > 1) {
      if (state.length > 1) {
         layout = state.pop();
         Plotly.relayout(GRAPH_DIV, state.pop());
      }
      else {
         layout = state.pop();
         layout = zoomedOut;
         Plotly.relayout(GRAPH_DIV, layout);
      }
   }
}

function hideAllChannels() {
   log('HideAll');
   doWork(() => {
      hidden = new Set(channels.map((c, i) => i));
      updateLegend(false, hidden);
   });
}

function showAllChannels() {
   log('ShowAll');
   doWork(() => {
      hidden = new Set();
      updateLegend(true, getShownIndices());
   });
}

const stack = () => {
   log('stack');
   doWork(() => {
      let axis = 1;
      if (!metadata) {
         channels.forEach((c, i) => data[i].yaxis = hidden.has(i) ? undefined : 'y' + axis++);
      } else {
         let units = {};
         channels.forEach((c, i) => {
            if (hidden.has(i)) {
               data[i].yaxis = undefined;
            } else {
               const unit = getUnit(c);
               if (!units[unit]) {
                  units[unit] = axis++;
               }
               data[i].yaxis = 'y' + units[unit];
            }
         });
      }
      Plotly.react(GRAPH_DIV, data, {
         grid: {
            rows: axis - 1,
            columns: 1
         },
         ...layout
      });
      stacked = true;
      storage.setItem('stacked', stacked.toString())
      updateState();
      updateUI();
   });
}

const unstack = () => {
   log('unstack');
   doWork(() => {
      channels.forEach((c, i) => data[i].yaxis = hidden.has(i) ? undefined : 'y');
      Plotly.react(GRAPH_DIV, data, {
         grid: {
            rows: 1,
            columns: 1
         },
         ...layout
      });
      stacked = false;
      storage.setItem('stacked', stacked.toString())
      updateState();
      updateUI();
   });
}

function downloadCsv() {
   log('Download CSV');
   let csvText = document.getElementById('csvText');
   let indices = getShownIndices();
   csvText.value = getCsv();
   let link = document.getElementById('link');
   link.onclick = function (_code) {
      link.href = 'data:text/plain;charset=utf-8,' + encodeURIComponent(csvText.value);
   };
   let filename = legend;
   if (!filename.toLowerCase().endsWith('.csv')) {
      filename += '.csv';
   }
   link.download = `${filename}.csv`;
   link.click();
   closeShareModal();
}

function getCsv() {
   let indices = getShownIndices();
   let contents = 'Timestamp,' + indices.map(i => channels[i]).join(',') + '\n';
   let t1 = new Date(Date.parse(layout.xaxis.range[0]));
   let t2 = new Date(Date.parse(layout.xaxis.range[1]));
   let csvData = '';

   // Take union of all data here...
   let pos = indices.map((_i) => 0);   // x index array
   let x = indices.map((i) => data[i].x.reduce((p, x) => x >= t1 && x <= t2 ? [...p, x.getTime()] : p, []));; // d.map(r => r.x.map(x => x.getTime()));
   let y = indices.map((i) => data[i].x.reduce((p, x, n) => x >= t1 && x <= t2 ? [...p, data[i].y[n]] : p, [])); // d.map(r => r.y);

   while (true) {
      let min_t = Math.min(...pos.map((p, i) => p < x[i].length ? x[i][p] : Number.MAX_VALUE));
      if (min_t === Number.MAX_VALUE) {
         break;
      }
      let new_row = pos.map((p, i) => p < x[i].length && x[i][p] === min_t ? y[i][p] : '');
      pos = pos.map((p, i) => p < x[i].length && x[i][p] === min_t ? p + 1 : p);
      csvData += new Date(min_t).toISOString() + ',' + new_row.join(',') + '\n';
   }

   contents += csvData;
   return contents;
}

function shareCsv(thumbnail) {
   log('Share CSV');
   const contents = getCsv();
   let filename = SHA256(contents).substring(0, 8);   // TODO: take longer part of the hash?
   uploadFile(filename + '.json', JSON.stringify({ filename: legend, stacked: stacked, mode: shapeIndex, legend: showLegend }));
   uploadFile(filename, contents)
      .then(response => {
         if (response.ok) {
            const { protocol, hostname } = window.location;
            const url = `${protocol}//${hostname}?share=${filename}${thumbnail === true ? '&thumbnail=1' : ''}`;
            console.log('File uploaded with URL ' + url);
            sendNotification('Plot shared with URL ' + url);
            window.open(url);
            navigator.clipboard.writeText(url);  // TODO: replace with url§
         } else {
            sendNotification('Failed to share plot');
         }
      })
      .catch(error => sendNotification('Failed to share plot (' + error.message + ')'));
   closeShareModal();
}

function downloadDataFrame() {
   // TODO: is it possible to copy to clipboard as well (instead?)
   // TODO: use doWork
   // TODO: add import izaxon etc.
   log('Download DataFrame');
   let dfText = document.getElementById('dfText');
   const indices = getShownIndices();
   // dfText.value = 'Timestamp,' + indices.map(i => channels[i]).join(',') + '\n';
   const t1 = new Date(Date.parse(layout.xaxis.range[0]));
   const t2 = new Date(Date.parse(layout.xaxis.range[1]));
   const rows = data[0].x.reduce((p, x, i) => x >= t1 && x <= t2 ? [...p, i] : p, []);
   const csvData = '[' + rows.map(r => '[' + ['"' + data[0].x[r].toISOString() + '"', ...indices.map(c => data[c].y[r])].join(',') + ']').join(',') + ']';
   // dfText.value += csvData;
   dfText.value = `df = pd.DataFrame(${csvData}, columns=['Timestamp',${indices.map(i => `'${channels[i]}'`).join(',')}])`;
   let link = document.getElementById('link3');
   link.onclick = function (_code) {
      link.href = 'data:text/plain;charset=utf-8,' + encodeURIComponent(dfText.value);
   };
   link.click();
   closeShareModal();
}

// TODO: improve this to start using hashed job inputs and cached job outputs...
/*const testSaveToCache = () => {
    const hash = hashCode(JSON.stringify({ 'plugin_input': 123 }));
    let transaction = files_db.transaction(['files_cache'], 'readwrite');
    let objectStore = transaction.objectStore('files_cache');
    objectStore.add({ id: hash.toString(), data: 'testfile.txt\n1, 2, 3\n' });
}*/

function downloadMetadata() {
   log('Download metadata');
   let jsonText = document.getElementById('jsonText');

   // Build metadata from all channels (with empty units) joined with existing metadata (having units)
   let md = {};
   const existingMetadata = getMetadata();
   channels.forEach(c => md[c] = existingMetadata[c] ? { unit: existingMetadata[c].unit || '', name: existingMetadata[c].name || c } : { unit: '', name: c });
   // md = { ...md, ...getMetadata() };
   jsonText.value = JSON.stringify(md, null, 2);
   let link = document.getElementById('link2');
   link.onclick = function (_code) {
      link.href = 'data:text/plain;charset=utf-8,' + encodeURIComponent(jsonText.value);
   };
   link.click();
   closeShareModal();
}

function loadOrMerge(csv) {
   if (confirm('Merge with existing data? (cancel will clear and open the new data)')) {
      log('merge');
      mergePlotData(csv);
   } else {
      log('load');
      loadAndPlotData(csv);
   }
}

function onPasteHandler(e) {
   log('Pasting...');
   const text = (e.clipboardData || window.clipboardData).getData('text');

   // TODO: is it an url? => then load CSV from it!
   if (text.startsWith('https://') && text.endsWith('.csv')) {
      // a url has been pasted
      log('paste csv url');
      sendNotification('Loading data from url = ' + text);
      fetch(text)
         .then(response => response.text())
         .then(csv => loadOrMerge(csv))
         .catch(error => console.warn('Failed to load CSV data from url', options.src));
   }
   else if (text.startsWith('https://') && text.endsWith('/plugin.json')) {
      log('Paste plugin json');
      // the url points to a potential plugin...
      runPlugin(text);
   }
   else {
      // TODO: is it CSV?
      log('Paste csv content');
      const { columns } = parseCsv(text); // TODO: this should not have to be run twice, make loadAndPlot data better (accept columns and channels?)
      const isCsv = columns.length >= 2 && columns[0].length > 3;
      if (isCsv) {
         // TODO: bring up alert/dialog (import/join or load/replace)
         e.preventDefault();
         const filename = (e.clipboardData || window.clipboardData).getFilename();
         setTitle(filename);
         loadOrMerge(text);
         // if (confirm('Merge with existing data? (cancel will clear and open the new data)')) {
         //    mergePlotData(text);
         // } else {
         //    loadAndPlotData(text);
         // }
      }
      else {
         log('Failed to parse pasted CSV contents');
         sendNotification("Failed to parse CSV contents from the clipboard!");
      }
   }
}

function getFilename() {
   return storage.getItem('last_filename') || 'xplot';
}

function downloadImage() {
   const { height, width } = document.getElementById('graph').style.height;
   Plotly.downloadImage(GRAPH_DIV, { format: 'png', width, height, filename: getFilename() });
   closeShareModal();
}

function printGraph() {
   closeShareModal();
   window.print();
}

function getChannelIndex(name) {
   return channels.indexOf(name);
}

function tryAddRealtimeChannel(name, x, y) {
   if (getChannelIndex(name) === -1) {
      const update = { name: name, x: x || [new Date()], y: y || [null], /*categoryorder: "category ascending", */type: 'scatter'/* TODO: 'category'*/, yaxis: 'y' };
      channels.push(name);
      data = [...data, update];
      if (stacked) {
         stack();
      }
      else {
         unstack();
      }
   }
}

function addNewRealtimeData(name, x, y) {
   const index = getChannelIndex(name)
   if (index === -1) {
      tryAddRealtimeChannel(name, x, y);
   }
   else {
      Plotly.extendTraces(GRAPH_DIV, { x: [x], y: [y] }, [index]);
   }
}

// TODO: function createLabelChannel() {
//    tryAddRealtimeChannel('Labels', data[0].x, )
// }

function labelData(name, range, label) {
   // console.log('about to label ' + label);
   const [x1, x2] = range;
   // const y = label;
   const index = getChannelIndex(name);
   // const t = data[0].x;
   let d = data[index];
   const [t1, t2] = [d.x[0], d.x[d.x.length - 1]];
   // let samplesToAdd = { x: [], y: [] };
   // let d = labelData.filter(s => s.x <= x2 && s.x >= x1);   // get timestamps to re-label

   // Re-label existing data points
   for (const i in d.x) {
      if (d.x[i] >= x1 && d.x[i] <= x2) {
         if (d.y[i] !== label) {
            d.y[i] = label;
            // console.log('re-labeled at ' + d.x[i]);
         }
      }
   }

   // Add new label at end (if outside existing data)
   if (x1 > t2) {
      // console.log('x1 and x2 appended');
      d.x = [...d.x, x1, x2];
      d.y = [...d.y, label, label];
   } else if (x2 > t2) {
      // console.log('x2 appended');
      d.x = [...d.x, x2];
      d.y = [...d.y, label];
   }

   // Add new label at beginning (if outside existing data)
   if (x2 < t1) {
      // console.log('x1 and x2 prepended');
      d.x = [x1, x2, ...d.x];
      d.y = [label, label, ...d.y];
   } else if (x1 < t1) {
      // console.log('x1 prepended');
      d.x = [x1, ...d.x];
      d.y = [label, ...d.y];
   }

   // let pos = d.x.filter(t => t < x1).length;
   // let rest = d.x.filter(t => t > x1).length;
   //if (pos + rest !== d.x.length - 1) {
   if (!d.x.some((x, i) => x.getTime() === x1.getTime())) {   // TODO: optimize
      // if (!d.x.some((x, i) => x.getTime() === x1.getTime() && d.y[i] === label)) {   // TODO: optimize
      const pos = d.x.filter(t => t.getTime() < x1.getTime()).length;
      // console.log('need to insert x1', pos);
      d.x.splice(pos, 0, x1);
      d.y.splice(pos, 0, label);
   }

   if (!d.x.some((x, i) => x.getTime() === x2.getTime())) {   // TODO: optimize
      // if (!d.x.some((x, i) => x.getTime() === x2.getTime() && d.y[i] === label)) {   // TODO: optimize
      const pos = d.x.filter(t => t.getTime() < x2.getTime()).length;
      // console.log('need to insert x2', pos);
      d.x.splice(pos, 0, x2);
      d.y.splice(pos, 0, label);
   }
   // pos = d.x.filter(t => t < x2).length;
   // rest = d.x.filter(t => t > x2).length;
   // if (pos + rest !== d.x.length - 1) {
   //    console.log('need to insert x2', pos);
   //    d.x.splice(pos, 0, x1);
   //    d.y.splice(pos, 0, label);
   // }
   data.splice(index, 1, d);
   // data = [...data]; 
   Plotly.react(GRAPH_DIV, data, { ...layout, datarevision: new Date().getTime() }, config);
   stack();

   buildModes();  // TODO: optimize => only add label channel to possible modes! 
   // if (stacked) {
   //    stack();
   // }
   // else {
   //    unstack();
   // }
   // let x = labelData.x.filter(ts => ts <)
   // console.log('length of all timestamps = ', t.length);
   // console.log('length timestamps to label = ', x.length);
   // for (const ts of x) {
   //    const index = labelData.x.indexOf(ts)
   //    if (index !== -1) { // timestamp already in label data
   //       labelData.x[index] = label;
   //    } else {
   //       samplesToAdd.x.push(ts);
   //       samplesToAdd.y.push(label);
   //    }
   // }

   // console.log('new data samples to label = ', samplesToAdd.x.length);
   // console.log('samples re-labeled = ', x.length - samplesToAdd.x.length);

   // if (samplesToAdd.x.length > 0) {
   //    addNewRealtimeData(name, samplesToAdd.x, samplesToAdd.y);
   // }
}

function onKeyDownHandler(e) {
   if (e.ctrlKey && e.code === 'KeyP') {
      // openQuickACtionsModal();
      e.preventDefault();
   } else {
      // console.log('onkeydown', e);
   }
}

function onKeyUpHandler(e) {
   if (e.ctrlKey && e.code === 'KeyP') {
      openQuickActionsModal();
   } else if (e.code === 'KeyN') {
      let newLegend = prompt('Rename?', legend);
      if (newLegend.trim() !== '') {
         setTitle(newLegend);
      }
   } else if (e.code === 'KeyO') {
      const fileElem = document.getElementById("fileElem");
      if (fileElem) {
         fileElem.click();
      }
   } else if (e.code === 'KeyU') {
      const fileElem3 = document.getElementById("fileElem3");
      if (fileElem3) {
         fileElem3.click();
      }
   } else if (e.code.startsWith('Digit')) {
      // const label = `${LABEL_NAME} ${e.code.substring(5)}`;
      const label = +e.code.substring(5);
      const x1 = new Date(Date.parse(layout.xaxis.range[0]));
      const x2 = new Date(Date.parse(layout.xaxis.range[1]) - 1); // minus 1 added to avoid overlapping labels
      if (getChannelIndex(LABEL_NAME) == -1) {
         if (!confirm('Start labeling?')) {
            return;
         }

         addNewRealtimeData(LABEL_NAME, [x1, x2], [label, label]);
         // addNewRealtimeData(LABEL_NAME, [data[0].x[0]], [null/*'Label 1'*/]);
         stack();
      }
      else {
         // const label = `${LABEL_NAME} ${e.code.substring(5)}`;
         // const x1 = new Date(Date.parse(layout.xaxis.range[0]));
         // const x2 = new Date(Date.parse(layout.xaxis.range[1]) - 1); // minus 1 added to avoid overlapping labels
         labelData(LABEL_NAME, [x1, x2], label);
      }
   } else if (e.code === 'KeyJ') {
      // addNewRealtimeData('Realtime data', [new Date()], [Math.random() * 10]);
      subscibeRealtimeData();
      // const wsUrl = prompt("Enter websocket url", "wss://localhost/");
      // if (wsUrl) {
      //    var ws = new WebSocket("wss://blackbox.local/");
      //    ws.onopen = () => {
      //       ws.onmessage = (event) => {
      //          const now = new Date();
      //          const data = JSON.parse(event.data);
      //          for (const key in data) {
      //             addNewRealtimeData(key, [now], [data[key]]);
      //          }
      //          console.log(new Date(), data);
      //       }
      //    };
      // }

      // Sample test
      // const name = LABEL_NAME;
      // const index = channels.indexOf(name)
      // addNewRealtimeData(LABEL_NAME, [data[0].x[0]], [null/*'Label 1'*/]);
      // stack();
      // if (index === -1) {
      //    log('adding traces');
      //    tryAddRealtimeChannel(name);
      //    // // console.log(data);
      //    // const update = { name: name, x: [new Date()], y: [Math.random()], type: 'scatter', yaxis: 'y' };
      //    // // Plotly.addTraces(GRAPH_DIV, update);
      //    // channels.push(name);
      //    // data = [...data, update];
      //    // if (stacked) {
      //    //    stack();
      //    // }
      //    // else {
      //    //    unstack();
      //    // }
      // }
      // else {
      //    // console.log(data);
      //    log('extending traces ' + index);
      //    Plotly.extendTraces(GRAPH_DIV, { x: [[new Date()]], y: [[Math.random()]] }, [index]);
      // }
   } else if (e.code === 'KeyH') {
      // downloadImage();
      // printGraph();
      // downloadCsv();
      // downloadMetadata();
      //downloadDataFrame();
      // TODO: copyDataFrame()
      // TODO: uploadAndCreateSharableLink() => use python docker instance for this?
      // TODO: shareEmbedHtmlCode() => upload + create link + create snippet HTML for sharing?
      // Get the modal
      if (e.shiftKey && e.ctrlKey) {
         shareCsv(true);
      } else if (e.shiftKey) {
         shareCsv();
      } else {
         let modal = document.getElementById("shareModal");
         modal.style.display = "block";
      }
   } else if (e.code === 'KeyS' && !e.shiftKey) {
      toggleStack();
   } else if (e.code === 'KeyA') {
      showAllChannels();
   } else if (e.code === 'KeyQ') {
      hideAllChannels();
   } else if (e.code === 'KeyF') {
      const filterElem = document.getElementById("channelFilter");
      filterElem.value = '';
      filterElem.focus();
   } else if (e.code === 'KeyT') {
      toggleTheme();
   } else if (e.code === 'KeyL') {
      toggleLegend();
   } else if (e.code === 'KeyV') {
      if (tabs.length > 0) {
         let index = storage.getItem('view_current');
         if (index !== null) {
            index = +index;
            index++;
            if (index === tabs.length) {
               index = 0;
            }
            selectTab(+index);
            selectView(+index);
         } else {
            selectTab(0);
            selectView(0);
         }
      }
   } else if (e.key === '+') {
      addView("view " + (tabs.length + 1))
   } else if (e.key === '-') {
      deleteView();
   } else if (['1', '2', '3', '4', '5', '6', '7', '8', '9'].includes(e.key) && +e.key <= tabs.length) {
      selectTab(+e.key - 1);
      selectView(+e.key - 1);
   } else if (e.code === 'KeyE') {
      downloadCsv();
   } else if (!e.ctrlKey && e.code === 'KeyM') {
      toggleMetadata();
   } else if (e.code === 'KeyZ') {
      toggleZenMode();
   } else if (e.code === 'ArrowLeft') {
      moveLeft();
   } else if (e.code === 'ArrowRight') {
      moveRight();
   } else if (e.ctrlKey && e.code === 'KeyM') {
      const fileElem2 = document.getElementById("fileElem2");
      if (fileElem2) {
         fileElem2.click();
      }
   } else if (!e.ctrlKey && e.code === 'KeyR') {
      toggleRangeslider();
      // } else if (e.code === 'KeyR') {
      //    const filesElem = document.getElementById("file_input");
      //    // filesElem.value = '';
      //    filesElem.focus();
      //    // filesElem.click();
   } else if (e.code === 'F1' && e.ctrlKey) {
      const errorLog = storage.getItem('error_log') || '[]'
      const supportText = JSON.parse(errorLog).join('\n');
      if (confirm(`Email the following log data to support?
      
${supportText}`)) {
         window.location.href = 'mailto:johan@izaxon.com?subject=XPlot%20Support&body=' + encodeURIComponent(supportText);
      }
   } else if (e.code === 'Escape') {
      closeAllModals();
      // closeMenu();
      // closeShareModal();
      // closeHelpModal();
   } else if (e.code === 'Space') {
      if (isMenuOpen()) {
         closeMenu();
      } else {
         openMenu();
      }
   } else {
      // console.log('onkeyup', e);
   }
}

const closeAllModals = () => {
   closeMenu();
   closeShareModal();
   closeHelpModal();
   closeQuickActionsModal();
}

const clearChannelFilter = () => {
   document.getElementById("channelFilter").value = '';
   document.getElementById('filterMatches').innerText = '';
   document.getElementById('buttonShow').hidden = false;
   document.getElementById('buttonHide').hidden = false;
   document.getElementById('buttonShowAll').hidden = true;
   document.getElementById('buttonHideAll').hidden = true;
}

const getChannelFilterHits = () => {
   const filterElem = document.getElementById("channelFilter");
   const pattern = filterElem.value;
   if (pattern.trim().length === 0) {
      return [];
   }

   const result = channels.map((ch, i) => {
      const fixedPattern = pattern
         .replace('(', '\\(')
         .replace(')', '\\)');
      let regex = new RegExp(fixedPattern, 'ig');
      return [regex.test(ch), i];
   });
   return result;
}

const toggleStack = () => {
   log('Toggle stack');
   if (stacked) {
      unstack();
   }
   else {
      stack();
   }
}

const updateStack = () => {
   if (stacked) {
      stack();
   }
}

const onChannelFilterKeyPress = (e) => {
   doWork(() => {
      const result = getChannelFilterHits();
      if (e.code === 'Enter') {
         const hits = result.filter(m => m[0]).map(m => m[1]);
         updateLegend(true, [...new Set(hits, getShownIndices())]);
         updateStack();
      } else if (e.code === 'Tab') {
         const filterElem = document.getElementById("channelFilter");
         filterElem.value = '';
         let div = document.getElementById("plot");
         div.focus();
      }
   });
}

const onChannelFilterKeyUp = (e) => {
   e.stopPropagation();
   const result = getChannelFilterHits();
   const length = result.filter(m => m[0]).length;
   document.getElementById('filterMatches').innerText = length;
   document.getElementById('buttonShow').hidden = !length;
   document.getElementById('buttonHide').hidden = !length;
   document.getElementById('buttonShowAll').hidden = !!length;
   document.getElementById('buttonHideAll').hidden = !!length;
};

const onQuickActionFilterKeyPress = (e) => {
   // doWork(() => {
   const hits = getQuickActionFilterHits();
   if (e.code === 'Enter') {
      hits[quickActionIndex][1]();
      closeQuickActionsModal();
   } else if (e.code === 'ArrowDown') {
      console.log('DOWN!');
   } else {
      // console.log(e.code);
   }
   // });
}

const onQuickActionClick = (index) => {
   const hits = getQuickActionFilterHits();
   hits[index][1]();
   closeQuickActionsModal();
}

const onQuickActionFilterKeyUp = (e) => {
   e.stopPropagation();
   const hits = getQuickActionFilterHits();
   // console.log(e.code);
   if (e.code === 'ArrowDown') {
      quickActionIndex++;
   } else if (e.code === 'ArrowUp') {
      quickActionIndex--;
   } else if (e.code === 'Escape') {
      closeQuickActionsModal();
   }

   quickActionIndex = Math.max(Math.min(quickActionIndex, hits.length - 1), 0);
   document.getElementById('actionMatches').innerHTML = hits.map((hit, i) => i === quickActionIndex ? `<div class="quickActionItemDiv"><a class="quickActionItem" onclick="onQuickActionClick(${i})"><b>${hit[0]}</b></a></div>` : `<div class="quickActionItemDiv"><a class="quickActionItem" onclick="onQuickActionClick(${i})">${hit[0]}</a></div>`).join('');
};

const updateLegend = (show, indices) => {
   doWork(() => {
      if (show) {
         Plotly.restyle(GRAPH_DIV, { visible: true, ...layout }, indices);
      }
      else {
         Plotly.restyle(GRAPH_DIV, { visible: showHiddenChannelsInLegend ? 'legendonly' : false, ...layout }, indices);
      }
   });
}

const show = () => {
   const result = getChannelFilterHits();
   const indices = result.filter(m => m[0]).map(m => m[1]);
   updateLegend(true, indices);
   clearChannelFilter();
   updateStack();
}

const hide = () => {
   const result = getChannelFilterHits();
   const indices = result.filter(m => m[0]).map(m => m[1]);
   const toHide = new Set(indices);
   hidden = new Set([...hidden].filter(x => !toHide.has(x)));  // TODO: move to "class" handling show/hidden etc. 
   updateLegend(false, indices);
   clearChannelFilter();
   updateStack();
}

const toggleType = () => {
   const shownIndices = channels.map((_, i) => i).filter(i => !hidden.has(i));
   if (shownIndices.length > 0) {
      Plotly.restyle(GRAPH_DIV, types[currentType], shownIndices);
      currentType++;
      if (currentType === types.length) {
         currentType = 0;
      }
   }
}

const toggleTheme = () => {
   log('Toggle theme');
   doWork(() => {
      darkTheme = !darkTheme;
      // layout = darkTheme ? themeDark : themeLight;
      layout = { ...layout, ...(darkTheme ? themeDark : themeLight) };
      layout.title.text = legend;
      Plotly.update(GRAPH_DIV, {}, { ...layout, showlegend: showLegend });
      storage.setItem('theme', darkTheme ? 'dark' : 'light');
      if (darkTheme) {
         document.body.className = "dark";
      } else {
         document.body.className = "light";
      }
   });
}

const toggleLegend = () => {
   log('Toggle legend');
   showLegend = !showLegend;
   // let checkboxLegend = document.getElementById("checkboxLegend");
   // checkboxLegend.disabled = !showLegend;
   layout = { ...layout, showlegend: showLegend };
   Plotly.update(GRAPH_DIV, {}, layout);
   storage.setItem('legend', showLegend.toString());
   updateState();
}

const subscibeRealtimeData = () => {
   const wsUrl = prompt("Enter websocket url", localStorage.getItem("wsUrl") || "ws://localhost/");
   if (wsUrl) {
      localStorage.setItem("wsUrl", wsUrl);
      var ws = new WebSocket(wsUrl);
      ws.onerror = (e) => {
         alert("Error: " + JSON.stringify(e));
      };

      ws.onopen = () => {
         ws.onmessage = (event) => {
            const now = new Date();
            const data = JSON.parse(event.data);
            for (const key in data) {
               addNewRealtimeData(key, [now], [data[key]]);
            }
            console.log(new Date(), data);
         }
      };
   }
}

const toggleRangeslider = () => {
   log('Toggle rangeslider');
   showRangeslider = !showRangeslider;
   const newLayout = { ...layout, ...{ xaxis: { ...layout.xaxis, rangeslider: { visible: showRangeslider } } } };
   Plotly.relayout(GRAPH_DIV, newLayout);
   storage.setItem('rangeslider', showRangeslider.toString());
}

const getUnit = (channelName) => {
   const md = getMetadata();
   if (md[channelName]) {
      return md[channelName].unit || '';
   }
   else {
      return '';
   }
}

const getName = (channelName) => {
   const md = getMetadata();
   if (md[channelName]) {
      return md[channelName].name || channelName;
   }
   else {
      return channelName;
   }
}

const showMetadata = () => {
   log('Show metadata');
   metadata = true;
   // document.getElementById("metadata").style.display = "block";
   const md = getMetadata();
   const formatUnit = (channelName) => {
      const unit = getUnit(channelName);
      if (unit) {
         return '(' + unit + ')';
      }
      else {
         return '';
      }
   };

   data.map((d, i) => d.name = `${getName(channels[i])} ${formatUnit(channels[i])}`);

   Plotly.react(GRAPH_DIV, data, layout, config);
   if (stacked) {
      stack();
   }
   else {
      unstack();
   }
}

const hideMetadata = () => {
   log('Hide metadata');
   metadata = false;
   // document.getElementById("metadata").style.display = "none";
   data.map((d, i) => d.name = channels[i]);
   Plotly.react(GRAPH_DIV, data, layout, config);
   if (stacked) {
      stack();
   }
   else {
      unstack();
   }
}

const toggleMetadata = () => {
   log('Toggle metadata');
   doWork(() => {
      if (metadata) {
         hideMetadata();
      }
      else {
         showMetadata();
      }
   });
}

const toggleZenMode = () => {
   log('Toggle zen mode');
   doWork(() => {
      let menu = document.getElementById("menubutton");
      let next = document.getElementById("next");
      let prev = document.getElementById("prev");
      if (zen) {
         menu.style = "display: block;";
         next.style = "display: block;";
         prev.style = "display: block;";
         zen = false;
         Plotly.update(GRAPH_DIV, {}, { showlegend: showLegend });
      }
      else {
         menu.style = "display: none;"
         next.style = "display: none;";
         prev.style = "display: none;";
         zen = true;
         Plotly.update(GRAPH_DIV, {}, { showlegend: false });
      }
   });
}

const move = (direction) => {
   log(`Move ${direction === -1 ? 'left' : 'right'}`);
   doWork(() => {
      if (layout.xaxis.range && layout.xaxis.range.length === 2) {
         const x1 = Date.parse(layout.xaxis.range[0]);
         const x2 = Date.parse(layout.xaxis.range[1]);
         const dx = (x2 - x1) * -direction;
         let range = [new Date(x1 - dx), new Date(x2 - dx)];
         const newLayout = { ...layout, xaxis: { ...layout.xaxis, range } };
         Plotly.relayout(GRAPH_DIV, newLayout);
      }
   });
}

const moveLeft = () => {
   move(-1);
}

const moveRight = () => {
   move(1);
}

const getMetadata = () => {
   try {
      let metadata = storage.getItem('metadata') || '{}';
      return JSON.parse(metadata);
   }
   catch {
      return {};
   }
}

const setMetadata = (metadata) => {
   storage.setItem('metadata', JSON.stringify(metadata));
}

const getModes = (index) => {
   if (index < 0 || index >= channels.length) {
      return [];
   }

   let shapeData = [];
   let lastMode = undefined;
   let x_1 = undefined;
   let modes = {};
   for (const i in data[index].x) {
      const x = data[index].x[i];
      const y = data[index].y[i];
      const numModes = Object.keys(modes).length;
      if (lastMode === undefined) {
         if (!(y in modes)) {
            modes[y] = numModes;
         }
         lastMode = { x0: x, mode: modes[y], y: y };
      } else if (lastMode.y !== y) {
         lastMode.x1 = x_1;
         shapeData.push(lastMode);
         if (!(y in modes)) {
            modes[y] = numModes;
         }
         lastMode = { x0: x, mode: modes[y], y: y };
      }

      if (lastMode && lastMode.y.match(/[a-z]/i)) {
         if (numModes > 40) { // texts...
            return [];
         }
      } else {
         if (numModes > 10) { // numbers... 
            // TODO: update max no of modes?
            return [];  // exit with no modes if to many modes detected!
         }
      }

      x_1 = x;
   }

   if (lastMode) {
      lastMode.x1 = x_1;
      shapeData.push(lastMode);
   }

   // TODO: remove this to show channels with one (1) mode as well...
   if (Object.keys(modes).length <= 1) {
      return [];
   }

   return shapeData;
}

const isModeChannel = (index) => {
   return getModes(index).length > 0;
}

const colorScale = ['#000083', '#0035A6', '#0288CB', '#04DFF1', '#4AFFB8', '#BAFF47', '#FED500', '#FC6300', '#EC0000', '#EC0000'];  // TODO: add colors

const hideShapes = () => {
   Plotly.relayout(GRAPH_DIV, { ...layout, shapes: [] });
}

const showShape = (index) => {
   doWork(() => {
      shapeIndex = index; // +e.target.value;
      const modes = getModes(shapeIndex);
      if (modes.length === 0) {
         Plotly.relayout(GRAPH_DIV, { ...layout, shapes: [] });
         return;
      }

      const shapes = modes.map(mode => ({
         type: 'rect',
         // x-reference is assigned to the x-values
         xref: 'x',
         // y-reference is assigned to the plot paper [0,1]
         yref: 'paper',
         x0: mode.x0,
         y0: 0,
         x1: mode.x1,
         y1: 1,
         fillcolor: colorScale[mode.mode % 10], // '#d3d3d3',
         opacity: 0.6, // 0.25, //0.2 + 0.07 * mode.mode,
         line: {
            width: 0
         },
         layer: 'below'
      }));

      const newLayout = {
         ...layout,
         shapes: shapes
         // [{
         //     type: 'rect',
         //     // x-reference is assigned to the x-values
         //     xref: 'x',
         //     // y-reference is assigned to the plot paper [0,1]
         //     yref: 'paper',
         //     x0: '2018-02-01',
         //     y0: 0,
         //     x1: '2018-03-01',
         //     y1: 1,
         //     fillcolor: '#d3d3d3',
         //     opacity: 0.2,
         //     line: {
         //         width: 0
         //     }
         // }]
      };
      Plotly.relayout(GRAPH_DIV, newLayout);
   });
}

const loadFile = (e) => {
   log('Load file');
   doWork(() => {
      const file = e.target.value;
      const files = existingFiles.filter(({ name }) => name === file);
      const hash = files[0].id;  // take first hit by name and get its id (=hash)
      let objectStore = files_db.transaction('files_store').objectStore('files_store');
      let request = objectStore.get(hash);
      request.onsuccess = () => {
         if (request.result) {
            const fileInput = document.getElementById('file_input');
            fileInput.value = '';
            loadAndPlotData(request.result.file);
            getViewsIfExisting();
            storage.setItem('last_file_hash', hash);
            tryGetState();
            updateStack();
         }
      };
   });
}

// TODO: make one openModel/closeModal impl that takes the id of the element as a parameter
const openShareModal = () => {
   let modal = document.getElementById("shareModal");
   modal.style.display = "block";
   closeMenu();
}

const closeShareModal = () => {
   let modal = document.getElementById("shareModal");
   modal.style.display = "none";
}

const openQuickActionsModal = () => {
   // buildQuickActions();
   quickActionIndex = 0;
   closeMenu();
   let modal = document.getElementById("quickActionsModal");
   modal.style.display = "block";
   let filterElem = document.getElementById("actionFilter");
   filterElem.value = '';
   filterElem.focus();
}

const closeQuickActionsModal = () => {
   let elem = document.getElementById("quickActionsModal");
   elem.style.display = "none";
}

const openHelpModal = () => {
   let modal = document.getElementById("helpModal");
   modal.style.display = "block";
   closeMenu();
}

const closeHelpModal = () => {
   let modal = document.getElementById("helpModal");
   modal.style.display = "none";
}

const openMenu = () => {
   closeShareModal();
   closeHelpModal();
   closeQuickActionsModal();
   document.getElementById("menu").style.display = "block";
}

const closeMenu = () => {
   document.getElementById("menu").style.display = "none";
}

const isMenuOpen = () => {
   return document.getElementById("menu").style.display === "block";
}

const renderHtml = ({ hideOpen, showHelp, zenMode, hideMetadata, hideTheme, hideRecent, hideModes }) => {
   const html = `<div id="graph" style="height:100%;" ondrop="dropHandler(event);" ondragover="dragOverHandler(event);">
   <span id="menubutton" class="menubutton" style="display: ${zenMode === true ? 'none' : 'block'};" onclick="openMenu()" title="Open Menu (Space)">&#9776;</span>
   <div id="menu_old" class="menu" style="top: 2; left:2; width: calc(100% - 400px); z-index: 1; position: absolute; display: ${zenMode === true ? 'none' : 'none'};">
   </div>
   <div id="menu" class="modal">
      <div id="menu_inner" class="sidenav">
         <div class="modal-header">
         <h3>XPlot</h3>
         </div>
         <div class="menu-body">
         <!--label style="font-size: 18px; margin: 4px;">XPlot</label-->
         <!--label style="font-size: 18px; margin: 4px; height: 8px;">&nbsp;</label>
         <br/-->
         <a href="javascript:void(0)" class="closebtn" onclick="closeMenu()" title="Close Menu (Esc/Space)">&times;</a>
         <button id="install-button" class="installbtn" style="display:none;" onclick="installApp()" title="Install XPlot app on my device">Install</button>
         </div>
         <input type="file" id="fileElem" accept="text/csv,.edf" style="display:none" multiple>
         <input type="file" id="fileElem2" accept="application/json" style="display:none">
         <input type="file" id="fileElem3" accept="text/csv" style="display:none">
         <div>
            <button id="fileSelect" ${hideOpen === true ? 'hidden ' : ''}title="Open CSV File (O)">Open...</button>
         </div>
         <div ${hideRecent === true ? 'hidden ' : ''}>
            <label for="file_input">Open recent</label>
            <input id="file_input" type="text" list="files_list" onChange="loadFile(event)" onkeyup="event.stopPropagation()">
            <datalist id="files_list">
               <select id="files">
               </select>
            </datalist>
         </div>
         <div>
            <button id="fileSelect3" ${hideOpen === true ? 'hidden ' : ''}title="Merge CSV File (U)">Merge...</button>
         </div>
         <div>
            <label for="checkboxStack" title="Stack/unstack channels (S)">Stack</label><input id="checkboxStack" type="checkbox" onclick="toggleStack()" style="vertical-align: middle;" title="Stack/unstack channels (S)"/>
         </div>
         <div>
            <label for="search">Filter</label><br/>
            <input type="search" id="channelFilter" onkeypress="onChannelFilterKeyPress(event)" onkeyup="onChannelFilterKeyUp(event)" title="Filter channels to show or hide (F)">
            <label id="filterMatches"></label>
            <button id="buttonShow" onclick="show()" hidden title="Show filtered channels">Show</button>
            <button id="buttonHide" onclick="hide()" hidden title="Hide filtered channels">Hide</button>
            <button id="buttonShowAll" onclick="showAllChannels()" title="Show all channels (A)">Show</button>
            <button id="buttonHideAll" onclick="hideAllChannels()" title="Hide all channels (Q)">Hide</button>
         </div>
         <div ${hideTheme === true ? 'hidden ' : ''}>
            <button id="buttonTheme" onclick="toggleTheme()" title="Toggle dark theme (T)">Toggle Theme</button>
         </div>
         <!--label for="checkboxLegend" title="Show full legend including hidden channels">Full Legend</label><input id="checkboxLegend" type="checkbox"
            onclick="toggleLegend()" /-->
         <div>
            <button id="buttonLegend" onclick="toggleLegend()" title="Toggle legend format (L)">Toggle Legend</button>
         </div>
         <div>
            <button id="buttonShare" onclick="openShareModal()" title="Open share dialog (H)">Share...</button>
         </div>
         <div ${hideMetadata === true ? 'hidden ' : ''}>
            <label for="checkboxMetadata" title="Toggle metadata (M)">Metadata</label><input id="checkboxMetadata" type="checkbox" onclick="toggleMetadata()" title="Toggle metadata (M)" ${hideMetadata === true ? 'hidden ' : ''}/>
            <button id="fileSelect2" title="Load metadata (CTRL+M)">Load metadata...</button>
         </div>
         <div ${hideModes === true ? 'hidden ' : ''}>
            <label for="modes">Mode</label>
            <select name="modes" id="modes" onChange="showShape(+event.target.value)">
               <option value="-1"></option>
            </select>
         </div>
         <div ${showHelp === true ? '' : 'hidden'}>
            <button id="help" title="Help" onClick="openHelpModal()">Help</button>
         </div>
         <div>
            <button id="quickActions" title="Quick actions (Ctrl+P)" onClick="openQuickActionsModal()">Quick actions</button>
         </div>
         <div style="display: none;" id="tabs" class="tab"></div>
      </div>
   </div>
   <a id="prev" class="prev" style="display: ${zenMode === true ? 'none' : 'block'};" onclick="moveLeft()" title="Scroll left (Left)">&#10094;</a>
   <a id="next" class="next" style="display: ${zenMode === true ? 'none' : 'block'};" onclick="moveRight()" title="Scroll right (Right)">&#10095;</a>
   <div id="txtWrap" style="display: none;"><textarea id="csvText"></textarea><a href="" id="link" download="data.csv">Download current view as CSV</a></div>
   <div id="txtWrap1" style="display: none;"><textarea id="jsonText"></textarea><a href="" id="link2" download="metadata.json">Download current view as JSON</a></div>
   <div id="txtWrap2" style="display: none;"><textarea id="dfText"></textarea><a href="" id="link3" download="dataframe.py.txt">Download current view as Python code</a></div>
   </div>
   <div id="loader" class="loader"></div>
   <label id="version">1.1.0</label>

   <div id="helpModal" class="modal">
   <div class="modal-content">
      <div class="modal-header">
         <span class="close" onClick="closeHelpModal()">&times;</span>
         <h3>Help</h3>
      </div>
      <div class="modal-body">
         <p>
            <label>Common commands</label>
            <div style="overflow: auto;">
               <ul>
                  <li>Quick actions (Ctrl+P)</li>
                  <li>Stack/unstack plots (S)</li>
                  <li>Show/hide menu (SPACE)</li>
                  <li>Open CSV (or Excel) file (O)</li>
                  <li>Show/hide legend (L)</li>
                  <li>Append another data file (U)</li>
                  <li>Show all channels (A)</li>
                  <li>Hide all channels (Q)</li>
                  <li>Share current (visible) plot (H)</li>
                  <li>Toggle range slider (R)</li>
                  <!--li>Toggle zen mode (Z)</li-->
                  <p>Missing some feature or have suggestions? Visit <a href="https://izaxon.github.io/xplot">https://izaxon.github.io/xplot</a>.</p>
               </ul>
            </div>
         </p>
      </div>
   </div>
   </div>

   <div id="quickActionsModal" class="modal">
      <div class="modal-content">
         <div class="modal-header">
            <span class="close" onClick="closeQuickActionsModal()">&times;</span>
            <h3>Quick Actions...</h3>
         </div>
         <div class="modal-body">
            <p>
               <input type="search" id="actionFilter" onkeypress="onQuickActionFilterKeyPress(event)" onkeyup="onQuickActionFilterKeyUp(event)" title="">
               <div id="actionMatches"></div>
               <!--select name="quickactions" id="quickactions" onChange="runQuickAction(event)">
               </select-->
            </p>
         </div>
      </div>
   </div>

   <div id="shareModal" class="modal">
   <div class="modal-content">
      <div class="modal-header">
        <span class="close" onClick="closeShareModal()">&times;</span>
        <h3>Share</h3>
      </div>
      <div class="modal-body">
         <p>
            <label>Share URL to plot graph (Shift + H)</label>
            <div style="overflow: auto;">
               <button style="float:right; width: 120px;" onClick="shareCsv()">Share</button>
            </div>
         </p>
         <p>
            <label>Share thumbnail URL</label>
            <div style="overflow: auto;">
               <button style="float:right; width: 120px;" onClick="shareCsv(true)">Thumbnail</button>
            </div>
         </p>
         <p>
            <label>Download graph as a CSV file</label>
            <div style="overflow: auto;">
               <button style="float:right; width: 120px;" onClick="downloadCsv()">Download CSV</button>
            </div>
         </p>
         <p>
            <label>Download graph image</label>
            <div style="overflow: auto;">
               <button style="float:right; width: 120px;" onClick="downloadImage()">Download Image</button>
            </div>
         </p>
         <p>
            <label>Print graph</label>
            <div style="overflow: auto;">
               <button style="float:right; width: 120px;" onClick="printGraph()">Print</button>
            </div>
         </p>
         <!--
         <p>
            <label>Download metadata file</label>
            <div style="overflow: auto;">
               <button style="float:right; width: 120px;" onClick="downloadMetadata()">Download Metadata</button>
            </div>
         </p>         
         <p>
            <label>Download Pandas DataFrame</label>
            <div style="overflow: auto;">
               <button style="float:right; width: 120px;" onClick="downloadDataFrame()">Download Data</button>
            </div>
         </p>
         -->
         <!--
         <p>
         <label>Share a link (URL) to current view</label>
         <div style="overflow: auto;">
         <button style="float:right; width: 120px;">Share Link</button>
         </div>
         </p>
         <p>
            <label>Copy embedded HTML snippet</label>
            <div style="overflow: auto;">
               <button style="float:right; width: 120px;">Share HTML</button>
            </div>
         </p>
         <p>
         <label>Share Jupyter notebook Python code snippet</label>
            <div style="overflow: auto;">
               <button style="float:right; width: 120px;">Share Code</button>
            </div>
         </p>
         -->
      </div>
      <!--div class="modal-footer">
         <button style="float:right;display:inline;overflow: auto;">Share</button>
         <button style="float:right;display:inline;overflow: auto;">Close</button>
      </div-->
   </div>
</div>`;
   let div = document.getElementById("plot");
   div.innerHTML = html;
}

function runPlugin(url) {
   // alert('running plugin from location ' + pluginUrl);
   // TODO: get plugin javascript source code or url to js file from parameters
   // TODO: get plugin info from url? (like package.json)
   // const pluginUrl = 'https://izaxon.github.io/plot/plugins/vsplot-plugin-sample';
   if (url !== 'https://test/plugin.json') {
      const pluginUrl = url.substring(0, url.lastIndexOf('/'));
      // const url = `${pluginUrl}/plugin.json`;
      var js;
      fetch(url)
         .then(response => response.json())
         .then(plugin_info => {
            const src = `${pluginUrl}/${plugin_info.main}`;
            (function (d, s, id) {
               var fjs = d.getElementsByTagName(s)[0];
               js = d.createElement(s);
               js.id = id;
               js.onload = function () {
                  try {
                     const indices = getShownIndices();
                     const input_data = indices.map(i => data[i]);
                     doWork(() => {
                        let csv = plugin({ data: input_data, metadata: getMetadata() });
                        mergePlotData(csv);
                        js.remove();
                     });
                  }
                  catch (error) {
                     sendNotification(`Failed to run plugin: ${error.message}`);
                     if (js) js.remove();
                  }
               };

               js.src = src;
               fjs.parentNode.insertBefore(js, fjs);
            }(document, 'script', 'plugin'));
         })
         .catch((error) => {
            sendNotification(`Failed to run plugin: ${error.message}`);
            if (js) js.remove();
         })
   }
   else {
      (function (d, s, id) {
         var fjs = d.getElementsByTagName(s)[0];
         // var elem = d.getElementById(id);
         // if (elem) { elem.remove(); }
         var js = d.createElement(s);
         js.id = id;
         js.onload = function () {
            try {
               // remote script has loaded
               // console.log('script loaded!');
               const indices = getShownIndices();
               const input_data = indices.map(i => data[i]);
               // console.log('data', data, input_data);
               let csv = plugin({ data: input_data, metadata: getMetadata() });
               // console.log(csv);
               mergePlotData(csv);
               console.log('plotted');
               js.remove();
            }
            catch (error) {
               sendNotification(`Failed to run plugin: ${error.message}`);
            }
         };
         // TODO: test js.innerHTML = ...
         js.src = "_plugin_sample.js";//"//connect.facebook.net/en_US/sdk.js";
         fjs.parentNode.insertBefore(js, fjs);
      }(document, 'script', 'plugin'));
   }
}
// const handleFiles = () => {
//    const fileList = this.files; /* now you can work with the file list */
//    // const numFiles = fileList.length;
//    // for (let i = 0, numFiles = fileList.length; i < numFiles; i++) {
//    //     const file = fileList[i];
//    //     // ...
//    // }

//    let fileReader = new FileReader();
//    fileReader.onload = e => {
//       if (files_db) { // TODO: https://developer.mozilla.org/en-US/docs/Learn/JavaScript/Client-side_web_APIs/Client-side_storage
//          const hash = hashCode(e.target.result);
//          // console.log('saving file to indexdb', hash);
//          let transaction = files_db.transaction(['files_store'], 'readwrite');
//          let objectStore = transaction.objectStore('files_store');
//          // TODO: check if file exists and update timestamp?
//          objectStore.add({ id: hash, name: fileList[0].name, file: e.target.result, timestamp: new Date().getTime() });
//          storage.setItem('last_file_hash', hash);
//       }

//       loadAndPlotData(e.target.result);
//       getViewsIfExisting();
//    }
//    fileReader.readAsText(fileList[0]);
// }

function handleFile(file) {
   let fileReader = new FileReader();
   fileReader.onload = e => {
      if (files_db) { // TODO: https://developer.mozilla.org/en-US/docs/Learn/JavaScript/Client-side_web_APIs/Client-side_storage
         const hash = hashCode(e.target.result);
         // console.log('saving file to indexdb', hash);
         let transaction = files_db.transaction(['files_store'], 'readwrite');
         let objectStore = transaction.objectStore('files_store');
         // TODO: check if file exists and update timestamp?
         objectStore.add({ id: hash, name: file.name, file: e.target.result, timestamp: new Date().getTime() });
         storage.setItem('last_file_hash', hash);
      }

      setTitle(file.name);
      loadAndPlotData(e.target.result);
      getViewsIfExisting();
      tryGetState();
   }
   fileReader.readAsText(file);
}

function handleMergeFile2(file) {
   let fileReader = new FileReader();
   fileReader.onload = e => {
      mergePlotData(e.target.result);
   };
   fileReader.readAsText(file);
}

const dropHandler = (ev) => {
   // Prevent default behavior (Prevent file from being opened)
   ev.preventDefault();

   if (ev.dataTransfer.items) {
      // Use DataTransferItemList interface to access the file(s)
      for (var i = 0; i < ev.dataTransfer.items.length; i++) {
         // If dropped items aren't files, reject them
         if (ev.dataTransfer.items[i].kind === 'file') {
            var file = ev.dataTransfer.items[i].getAsFile();
            // console.log('... file[' + i + '].name = ' + file.name);
            if (ev.ctrlKey || i > 0) {
               handleMergeFile2(file);
            } else {
               handleFile(file);
            }
         }
      }
   } else {
      // Use DataTransfer interface to access the file(s)
      for (var i = 0; i < ev.dataTransfer.files.length; i++) {
         // console.log('... file[' + i + '].name = ' + ev.dataTransfer.files[i].name);
         if (ev.ctrlKey || i > 0) {
            handleMergeFile2(file);
         } else {
            handleFile(file);
         }
      }
   }
}

const dragOverHandler = (ev) => {
   ev.preventDefault();
}

const downloadFile = (filename) => fetch(`https://functions.izaxon.com/download?filename=${filename}`);

const uploadFile = (filename, contents) => {
   let formData = new FormData();
   formData.append("file", new Blob([contents]), filename);
   return fetch("https://functions.izaxon.com/upload", {
      "method": "POST",
      "headers": {
         "user-agent": "vscode-restclient"
      },
      body: formData
   });
}

const initialize_timeseries_plot = (options) => {
   options = options || {};
   plotOptions = options;
   renderHtml(options);

   if (options.data) {
      loadAndPlotData(options.data);
   } else if (options.url) {
      fetch(options.url)
         .then(response => response.text())
         .then(csv => loadAndPlotData(csv))
         .catch(_error => console.warn('Failed to load CSV data from url', options.url));
   } else if (options.share) {
      downloadFile(options.share)
         .then(response => response.text())
         .then(csv => loadAndPlotDataSync(csv))
         // .catch(_error => console.warn('Failed to load CSV data from share link', options.share));
         .then(() => downloadFile(options.share + '.json'))
         //downloadFile(options.share + '.json')
         .then(response => response.json())
         .then(json => {
            setTitle(json.filename);
            console.log(json);
            if (json.stacked === true) {
               if (!stacked) stack();
            } else if (json.stacked === false) {
               if (stacked) unstack();
            }

            if (json.mode !== undefined) {
               const mode = json.mode - 1;
               const modesElem = document.getElementById('modes');
               modesElem.value = mode.toString();
               showShape(mode);
            }

            if (json.legend === true) {
               if (!legend) toggleLegend();
            } else if (json.stacked === false) {
               if (legend) toggleLegend();
            }

            setTimeout(checkCreateThumbnail, 1000);
         })
         .catch(() => console.log('No title/legend found for file'));
   }

   document.body.onkeyup = onKeyUpHandler;
   document.body.onkeydown = onKeyDownHandler;
   document.body.onpaste = onPasteHandler;

   if (document.readyState === 'complete') {
      onLoad(options);
   } else {
      window.addEventListener('load', () => onLoad(options), { once: true });
   }

   const fileSelect = document.getElementById("fileSelect");
   const fileSelect2 = document.getElementById("fileSelect2");
   const fileSelect3 = document.getElementById("fileSelect3");
   const fileElem = document.getElementById("fileElem");   // text/csv
   const fileElem2 = document.getElementById("fileElem2"); // application/json
   const fileElem3 = document.getElementById("fileElem3"); // file merge

   function clickFileElem() {
      if (fileElem) {
         fileElem.click();
         closeMenu();
      }
   }

   function clickFileElem2() {
      if (fileElem2) {
         fileElem2.click();
         closeMenu();
      }
   }

   function clickFileElem3() {
      if (fileElem3) {
         fileElem3.click();
         closeMenu();
      }
   }

   fileSelect.addEventListener("click", function (e) {
      clickFileElem();
   }, false);

   fileSelect2.addEventListener("click", function (e) {
      clickFileElem2();
   }, false);

   fileSelect3.addEventListener("click", function (e) {
      clickFileElem3();
   }, false);

   function handleMergeFile() {
      // TODO: support multiple files?
      // TODO: share code with handleFiles
      const fileList = this.files; /* now you can work with the file list */
      if (fileList.length > 0) {
         const file = fileList[0];
         const ext = file.name.substring(file.name.lastIndexOf('.')).toLowerCase();
         let fileReader = new FileReader();
         fileReader.onload = e => {
            mergePlotData(e.target.result);
         };
         fileReader.readAsText(file);
      }
   }

   function handleFiles() {
      const fileList = this.files; /* now you can work with the file list */
      // const numFiles = fileList.length;
      // for (let i = 0, numFiles = fileList.length; i < numFiles; i++) {
      //     const file = fileList[i];
      //     // ...
      // }
      // console.log(fileList);
      const file = fileList[0];
      const ext = file.name.substring(file.name.lastIndexOf('.')).toLowerCase();
      let fileReader = new FileReader();
      switch (ext) {
         case '.csv':
            fileReader.onload = e => {
               if (files_db) { // TODO: https://developer.mozilla.org/en-US/docs/Learn/JavaScript/Client-side_web_APIs/Client-side_storage
                  const hash = hashCode(e.target.result);
                  // console.log('saving file to indexdb', hash);
                  let transaction = files_db.transaction(['files_store'], 'readwrite');
                  let objectStore = transaction.objectStore('files_store');
                  // TODO: check if file exists and update timestamp?
                  const filename = fileList[0].name;
                  objectStore.add({ id: hash, name: filename, file: e.target.result, timestamp: new Date().getTime() });
                  storage.setItem('last_file_hash', hash);
                  storage.setItem('last_filename', filename);
                  setTitle(filename);
               }

               loadAndPlotData(e.target.result);
               getViewsIfExisting();
               tryGetState();
            };
            fileReader.readAsText(fileList[0]);
            break;
         case '.edf':
            fileReader.onload = e => {
               const data = new Uint8Array(e.target.result);
               let edf = new EDF(data);
               // console.log("DateTime:", edf.date, edf.time);
               // console.log("Duration:", edf.duration, "seconds");
               // console.log("Has annotations:", edf.has_annotations);
               // console.log("Channel count:", edf.realChannelCount)

               const dt = edf.data_record_duration;
               const [dd, mm, yy] = edf.date.split('.');
               const [hh, minutes, ss] = edf.time.split('.');
               const t = new Date(+yy < 85 ? 2000 + +yy : 1900 + +yy, +mm, +dd, +hh, +minutes, +ss);
               const samples = edf.read(0, edf.duration);

               let channels = [];
               for (let i = 0; i < edf.realChannelCount; i++) {
                  channels.push(edf.channels[i].label);
               }

               let csv = "Timestamp," + channels.join(',');
               for (let i = 0; i < samples[0].length; i++) {
                  csv += '\n' + t.toISOString() + ',' + samples.map(s => s[i]).join(',');
                  t.setTime(t.getTime() + dt * 1000);
               }

               setTitle(fileList[0].name);
               loadAndPlotData(csv);
            };
            fileReader.readAsArrayBuffer(fileList[0]);
            break;
         case '.xls':
         case '.xlsx':
            var filename = file.name;
            let formData = new FormData();
            formData.append("file", fileList[0], filename);
            fetch("https://functions.izaxon.com/excel2csv", {
               "method": "POST",
               "headers": {
                  "user-agent": "vscode-restclient"
               },
               body: formData
            })
               .then(response => response.text())
               .then(contents => {
                  console.log(contents);
                  if (files_db) { // TODO: https://developer.mozilla.org/en-US/docs/Learn/JavaScript/Client-side_web_APIs/Client-side_storage
                     const hash = hashCode(contents);
                     let transaction = files_db.transaction(['files_store'], 'readwrite');
                     let objectStore = transaction.objectStore('files_store');
                     // TODO: check if file exists and update timestamp?
                     objectStore.add({ id: hash, name: filename, file: contents, timestamp: new Date().getTime() });
                     storage.setItem('last_file_hash', hash);
                     storage.setItem('last_filename', filename);
                     setTitle(filename);
                  }

                  loadAndPlotData(contents);
                  getViewsIfExisting();
                  tryGetState();
               })
               .catch(err => {
                  // TODO: handle!
                  console.error(err);
               });
            break;
      };

      // If fileList contains more than one file then merge the ones following the first
      for (let n = 1; n < fileList.length; n++) {
         let fileReader2 = new FileReader();
         // TODO: switch csv vs. xls* here as well...
         fileReader2.onload = e => {
            mergePlotData(e.target.result);
         };

         fileReader2.readAsText(fileList[n]);
      }
   }

   // const dropHandler = (ev) => {
   //    console.log('File(s) dropped');

   //    // Prevent default behavior (Prevent file from being opened)
   //    ev.preventDefault();

   //    if (ev.dataTransfer.items) {
   //       // Use DataTransferItemList interface to access the file(s)
   //       for (var i = 0; i < ev.dataTransfer.items.length; i++) {
   //          // If dropped items aren't files, reject them
   //          if (ev.dataTransfer.items[i].kind === 'file') {
   //             var file = ev.dataTransfer.items[i].getAsFile();
   //             console.log('... file[' + i + '].name = ' + file.name);

   //             this.files = [file];
   //             handleFiles();
   //             // loadAndPlotData(file);
   //          }
   //       }
   //    } else {
   //       // Use DataTransfer interface to access the file(s)
   //       for (var i = 0; i < ev.dataTransfer.files.length; i++) {
   //          console.log('... file[' + i + '].name = ' + ev.dataTransfer.files[i].name);
   //          this.files = [file];
   //          handleFiles();
   //          // loadAndPlotData(file);
   //       }
   //    }
   // }

   // const dragOverHandler = (ev) => {
   //    ev.preventDefault();
   // }

   function loadMetadata() {
      const fileList = this.files;
      let fileReader = new FileReader();
      fileReader.onload = e => {
         const json = e.target.result;
         let md = getMetadata();
         md = { ...md, ...JSON.parse(json) };
         setMetadata(md);
         metadata = true;
         showMetadata();
         updateUI();
      }

      fileList.forEach(f => fileReader.readAsText(f));
   }

   fileElem.addEventListener("change", handleFiles, false);
   fileElem2.addEventListener("change", loadMetadata, false);
   fileElem3.addEventListener("change", handleMergeFile, false);

   window.addEventListener('beforeinstallprompt', (e) => {
      console.log('beforeinstallprompt', e);
      deferredPrompt = e;
      let elem = document.getElementById('install-button');
      if (elem) {
         elem.style = "display: block;"
      }
   })
};

// Inline handlers in the generated markup resolve names on the page.
Object.assign(window, {
   initialize_timeseries_plot,
   openMenu,
   closeMenu,
   installApp,
   loadFile,
   toggleStack,
   onChannelFilterKeyPress,
   onChannelFilterKeyUp,
   show,
   hide,
   showAllChannels,
   hideAllChannels,
   toggleTheme,
   toggleLegend,
   openShareModal,
   closeShareModal,
   toggleMetadata,
   showShape,
   openHelpModal,
   closeHelpModal,
   openQuickActionsModal,
   closeQuickActionsModal,
   onQuickActionFilterKeyPress,
   onQuickActionFilterKeyUp,
   onQuickActionClick,
   moveLeft,
   moveRight,
   shareCsv,
   downloadCsv,
   downloadImage,
   printGraph,
   dropHandler,
   dragOverHandler
});

