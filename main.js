function fetchAndInstantiate(url, imports = {}) {
  return WebAssembly.instantiateStreaming(fetch(url), imports).then(response => {
    return response.instance;
  }).catch(console.error);
}

async function main() {
  const main = await fetchAndInstantiate("main.wasm", {env:{load, symbol, console_log_u32: res => console.log("Lazy foo Result: " + res), 
      console_log_f64: res => console.log("Lazy bar Result: " + res)}} );
  console.log(main.exports)
  window.main = main;
  const container = document.getElementById("container");
  container.innerHTML = main.exports.__run__();//add(1, 2);

  // const button = document.getElementById("button");
  // button.onclick = async function() {
  //   console.log(main.exports.memory)
  //   const lazy = await fetchAndInstantiate("lazy.wasm", {
  //     main: {
  //       memory: main.exports.memory
  //     }
  //   });
  //   document.getElementById("container").innerHTML += "<br/>" ;//+ lazy.exports.get_add_result();
  // };
}

main();
